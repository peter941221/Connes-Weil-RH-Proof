import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541
import ConnesWeilRH.Dev.C1RouteABoundaryMidpoint2548

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem firstJetMidpoint_triangle2563 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

theorem fjmidZero2563 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def fjmidP000Center2563 : RatPair2542 := (0, 0)

def fjmidP000Factor2563 : RatPair2542 := (0, 0)

noncomputable def fjmidP000Error2563 : ℝ := 0

theorem fjmidP000Exterior2563 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 = 0 := by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |edgeMidpointPosition2548| := by
    norm_num [storedWidth, edgeMidpointPosition2548]
  exact weightedFamily_outside_zero2543 n (1/2)
    (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem fjmidP000BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP000Center2563‖ ≤ fjmidP000Error2563 := by
  rw [fjmidP000Exterior2563]
  norm_num [fjmidP000Center2563, fjmidP000Error2563, fjmidZero2563]

theorem fjmidP000DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP000Factor2563 * embedPair2542 fjmidP000Center2563‖ ≤
        (pairMagnitude2542 fjmidP000Factor2563 : ℝ) * fjmidP000Error2563 := by
  rw [fjmidP000Exterior2563]
  norm_num [fjmidP000Factor2563, fjmidP000Center2563, fjmidP000Error2563, pairMagnitude2542,
      fjmidZero2563]

def fjmidP000Rounded2563 : RatPair2542 := (0, 0)

noncomputable def fjmidP000Radius2563 : ℝ := 0

theorem fjmidP000RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP000Factor2563 fjmidP000Center2563) = fjmidP000Rounded2563 :=
        by
  cbv

theorem fjmidP000RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP000Rounded2563‖ ≤ fjmidP000Radius2563 := by
  rw [fjmidP000Exterior2563]
  norm_num [fjmidP000Rounded2563, fjmidP000Radius2563, fjmidZero2563]

theorem fjmidP000DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  rw [fjmidP000Exterior2563]
  norm_num

noncomputable def fjmidP001Input2563 : RatPair2542 := ((((-((75 * 10^40
        + 5793610062624408994825365663891066264162) * 10^40
        + 9918580294757314292856548188915782259599)) : ℚ) /
        ((208 * 10^40
        + 8043940912794372598641292711490528776820) * 10^40
        + 5100987153752063079186153183641600000000)),
    ((1751911280236833479653958331 : ℚ) /
        7378697629483820646400000000))

def fjmidP001Center2563 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def fjmidP001Factor2563 : RatPair2542 := ((((((48285684764685279210 * 10^40
        + 694469654141666716653755739374361511957) * 10^40
        + 1983023933887071209369055503369610426160) * 10^40
        + 7153470032678510502599646667891762695281) : ℚ) /
        (((79306619212413954 * 10^40
        + 6135590275954697994891057369985995860880) * 10^40
        + 3799340399814374588299513654302616835559) * 10^40
        + 5354338069519581005199293335783525390562)),
    (((-5524291025718029) : ℚ) /
        140737488355328))

noncomputable def fjmidP001Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP001BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP001Center2563‖ ≤ fjmidP001Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP001Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP001Input2563]
  have hc : (compactExp2547 fjmidP001Input2563 9).1 = fjmidP001Center2563 := by cbv
  have he : ((compactExp2547 fjmidP001Input2563 9).2 : ℝ) = fjmidP001Error2563 := by
    have hq : (compactExp2547 fjmidP001Input2563 9).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP001Error2563]
  have h := compactExp_error2547 fjmidP001Input2563 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^9 * embedPair2542 fjmidP001Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP001Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP001DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP001Factor2563 * embedPair2542 fjmidP001Center2563‖ ≤
        (pairMagnitude2542 fjmidP001Factor2563 : ℝ) * fjmidP001Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP001Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP001Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP001BaseError2563
    (embedPair_magnitude2542 fjmidP001Factor2563)

def fjmidP001Rounded2563 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP001Radius2563 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP001RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP001Factor2563 fjmidP001Center2563) = fjmidP001Rounded2563 :=
        by
  cbv

theorem fjmidP001RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP001Rounded2563‖ ≤ fjmidP001Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP001Factor2563 fjmidP001Center2563)
  rw [fjmidP001RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP001Factor2563 * embedPair2542 fjmidP001Center2563)
    (embedPair2542 fjmidP001Rounded2563)).trans (add_le_add fjmidP001DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP001Factor2563, fjmidP001Error2563, rounding2542,
      fjmidP001Radius2563]

theorem fjmidP001DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP001Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP001RoundedError2563 (embedPair_magnitude2542
      fjmidP001Rounded2563))
  apply h'.trans
  norm_num [fjmidP001Radius2563, pairMagnitude2542, fjmidP001Rounded2563]

noncomputable def fjmidP002Input2563 : RatPair2542 := ((((-((2007 * 10^40
        + 5023240729250299860289918989155247824672) * 10^40
        + 8628363056985938976693269865273365762959)) : ℚ) /
        ((8147 * 10^40
        + 6895918656149932623563298325318453465194) * 10^40
        + 9452298146475584633489225469132800000000)),
    (((-1751911280236833479653958331) : ℚ) /
        3689348814741910323200000000))

def fjmidP002Center2563 : RatPair2542 := ((((-339364505114828529043) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-241773850067246350091) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def fjmidP002Factor2563 : RatPair2542 := ((((((20410471496658769252947 * 10^40
        + 201616653836564308804866838098672716556) * 10^40
        + 8352564845593485597351628508576556609708) * 10^40
        + 1861792055619879599051472905736806632561) : ℚ) /
        (((483013323431043476903 * 10^40
        + 7511499335200218287611909907279225454881) * 10^40
        + 746082615335519961120361053248712426867) * 10^40
        + 9194345188221519198102945811473613265122)),
    ((5524291025718029 : ℚ) /
        140737488355328))

noncomputable def fjmidP002Error2563 : ℝ := ((2191587035296828369 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP002BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP002Center2563‖ ≤ fjmidP002Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP002Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP002Input2563]
  have hc : (compactExp2547 fjmidP002Input2563 8).1 = fjmidP002Center2563 := by cbv
  have he : ((compactExp2547 fjmidP002Input2563 8).2 : ℝ) = fjmidP002Error2563 := by
    have hq : (compactExp2547 fjmidP002Input2563 8).2 =
        ((2191587035296828369 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP002Error2563]
  have h := compactExp_error2547 fjmidP002Input2563 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^8 * embedPair2542 fjmidP002Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP002Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP002DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP002Factor2563 * embedPair2542 fjmidP002Center2563‖ ≤
        (pairMagnitude2542 fjmidP002Factor2563 : ℝ) * fjmidP002Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP002Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP002Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP002BaseError2563
    (embedPair_magnitude2542 fjmidP002Factor2563)

def fjmidP002Rounded2563 : RatPair2542 :=
  (((503 : ℚ) /
        158456325028528675187087900672),
    (((-29277) : ℚ) /
        1267650600228229401496703205376))

noncomputable def fjmidP002Radius2563 : ℝ := ((2199023255707 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP002RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP002Factor2563 fjmidP002Center2563) = fjmidP002Rounded2563 :=
        by
  cbv

theorem fjmidP002RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP002Rounded2563‖ ≤ fjmidP002Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP002Factor2563 fjmidP002Center2563)
  rw [fjmidP002RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP002Factor2563 * embedPair2542 fjmidP002Center2563)
    (embedPair2542 fjmidP002Rounded2563)).trans (add_le_add fjmidP002DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP002Factor2563, fjmidP002Error2563, rounding2542,
      fjmidP002Radius2563]

theorem fjmidP002DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP002Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP002RoundedError2563 (embedPair_magnitude2542
      fjmidP002Rounded2563))
  apply h'.trans
  norm_num [fjmidP002Radius2563, pairMagnitude2542, fjmidP002Rounded2563]

noncomputable def fjmidP003Input2563 : RatPair2542 := ((((-((7224110 * 10^40
        + 4406628376595866370136231705353501324162) * 10^40
        + 1511332573809066646429207955160645591911)) : ℚ) /
        ((39860431 * 10^40
        + 3525369205518296877772896888819194996209) * 10^40
        + 8027785848626107559175480881971200000000)),
    (((-1751911280236833479653958331) : ℚ) /
        3689348814741910323200000000))

def fjmidP003Center2563 : RatPair2542 := ((((-5949091438372091633409808421) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-132447442184126730267608627) : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)))

def fjmidP003Factor2563 : RatPair2542 := ((((((171489622156943000195426447198 * 10^40
        + 6062598187743684290659208420886884284629) * 10^40
        + 1535621732405997006189222369556390501971) * 10^40
        + 5719713847345472865924858164472905824001) : ℚ) /
        (((11560434268978921445520672852 * 10^40
        + 3151491610707945740034502288795420775469) * 10^40
        + 9342842308133684351566010846049001848136) * 10^40
        + 2052163694690945731849716328945811648002)),
    ((5524291025718029 : ℚ) /
        140737488355328))

noncomputable def fjmidP003Error2563 : ℝ := ((17997678379747832815547905 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem fjmidP003BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP003Center2563‖ ≤ fjmidP003Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP003Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP003Input2563]
  have hc : (compactExp2547 fjmidP003Input2563 8).1 = fjmidP003Center2563 := by cbv
  have he : ((compactExp2547 fjmidP003Input2563 8).2 : ℝ) = fjmidP003Error2563 := by
    have hq : (compactExp2547 fjmidP003Input2563 8).2 =
        ((17997678379747832815547905 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by cbv
    rw [hq]
    norm_num [fjmidP003Error2563]
  have h := compactExp_error2547 fjmidP003Input2563 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^8 * embedPair2542 fjmidP003Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP003Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP003DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP003Factor2563 * embedPair2542 fjmidP003Center2563‖ ≤
        (pairMagnitude2542 fjmidP003Factor2563 : ℝ) * fjmidP003Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP003Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP003Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP003BaseError2563
    (embedPair_magnitude2542 fjmidP003Factor2563)

def fjmidP003Rounded2563 : RatPair2542 :=
  (((53012890685 : ℚ) /
        316912650057057350374175801344),
    (((-77902180797) : ℚ) /
        316912650057057350374175801344))

noncomputable def fjmidP003Radius2563 : ℝ := ((550177973521 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem fjmidP003RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP003Factor2563 fjmidP003Center2563) = fjmidP003Rounded2563 :=
        by
  cbv

theorem fjmidP003RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP003Rounded2563‖ ≤ fjmidP003Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP003Factor2563 fjmidP003Center2563)
  rw [fjmidP003RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP003Factor2563 * embedPair2542 fjmidP003Center2563)
    (embedPair2542 fjmidP003Rounded2563)).trans (add_le_add fjmidP003DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP003Factor2563, fjmidP003Error2563, rounding2542,
      fjmidP003Radius2563]

theorem fjmidP003DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP003Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP003RoundedError2563 (embedPair_magnitude2542
      fjmidP003Rounded2563))
  apply h'.trans
  norm_num [fjmidP003Radius2563, pairMagnitude2542, fjmidP003Rounded2563]

noncomputable def fjmidP004Input2563 : RatPair2542 := ((((-((4673 * 10^40
        + 4597880448384906672533435637131642652828) * 10^40
        + 431693750250106491058255045937428262959)) : ℚ) /
        ((29780 * 10^40
        + 5895054484312759971766663273404887092534) * 10^40
        + 1331668037402944633489225469132800000000)),
    ((1751911280236833479653958331 : ℚ) /
        3689348814741910323200000000))

def fjmidP004Center2563 : RatPair2542 := ((((-1498581575969300851911523103931) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((4270544877866285909173470095625 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def fjmidP004Factor2563 : RatPair2542 := ((((((49506120272990836016484 * 10^40
        + 538440731705255384998620093587205991356) * 10^40
        + 1801622978639223413569344746755076688363) * 10^40
        + 9685227492010182942675068950658681632561) : ℚ) /
        (((6452926836878943435502 * 10^40
        + 5270363476754729271482605203204217239397) * 10^40
        + 2433289965035647104971396368485606800583) * 10^40
        + 9158788578070925885350137901317363265122)),
    (((-5524291025718029) : ℚ) /
        140737488355328))

noncomputable def fjmidP004Error2563 : ℝ := ((17699073006843670952439380847 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP004BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP004Center2563‖ ≤ fjmidP004Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP004Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP004Input2563]
  have hc : (compactExp2547 fjmidP004Input2563 8).1 = fjmidP004Center2563 := by cbv
  have he : ((compactExp2547 fjmidP004Input2563 8).2 : ℝ) = fjmidP004Error2563 := by
    have hq : (compactExp2547 fjmidP004Input2563 8).2 =
        ((17699073006843670952439380847 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP004Error2563]
  have h := compactExp_error2547 fjmidP004Input2563 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^8 * embedPair2542 fjmidP004Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP004Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP004DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP004Factor2563 * embedPair2542 fjmidP004Center2563‖ ≤
        (pairMagnitude2542 fjmidP004Factor2563 : ℝ) * fjmidP004Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP004Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP004Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP004BaseError2563
    (embedPair_magnitude2542 fjmidP004Factor2563)

def fjmidP004Rounded2563 : RatPair2542 :=
  (((62725627062873 : ℚ) /
        633825300114114700748351602688),
    ((16307390202537 : ℚ) /
        158456325028528675187087900672))

noncomputable def fjmidP004Radius2563 : ℝ := ((2919382120955 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP004RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP004Factor2563 fjmidP004Center2563) = fjmidP004Rounded2563 :=
        by
  cbv

theorem fjmidP004RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP004Rounded2563‖ ≤ fjmidP004Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP004Factor2563 fjmidP004Center2563)
  rw [fjmidP004RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP004Factor2563 * embedPair2542 fjmidP004Center2563)
    (embedPair2542 fjmidP004Rounded2563)).trans (add_le_add fjmidP004DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP004Factor2563, fjmidP004Error2563, rounding2542,
      fjmidP004Radius2563]

theorem fjmidP004DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP004Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP004RoundedError2563 (embedPair_magnitude2542
      fjmidP004Rounded2563))
  apply h'.trans
  norm_num [fjmidP004Radius2563, pairMagnitude2542, fjmidP004Rounded2563]

def fjmidP005Center2563 : RatPair2542 := (0, 0)

def fjmidP005Factor2563 : RatPair2542 := (0, 0)

noncomputable def fjmidP005Error2563 : ℝ := 0

theorem fjmidP005Exterior2563 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 = 0 := by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |edgeMidpointPosition2548| := by
    norm_num [storedWidth, edgeMidpointPosition2548]
  exact weightedFamily_outside_zero2543 n (1/2)
    (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem fjmidP005BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP005Center2563‖ ≤ fjmidP005Error2563 := by
  rw [fjmidP005Exterior2563]
  norm_num [fjmidP005Center2563, fjmidP005Error2563, fjmidZero2563]

theorem fjmidP005DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP005Factor2563 * embedPair2542 fjmidP005Center2563‖ ≤
        (pairMagnitude2542 fjmidP005Factor2563 : ℝ) * fjmidP005Error2563 := by
  rw [fjmidP005Exterior2563]
  norm_num [fjmidP005Factor2563, fjmidP005Center2563, fjmidP005Error2563, pairMagnitude2542,
      fjmidZero2563]

def fjmidP005Rounded2563 : RatPair2542 := (0, 0)

noncomputable def fjmidP005Radius2563 : ℝ := 0

theorem fjmidP005RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP005Factor2563 fjmidP005Center2563) = fjmidP005Rounded2563 :=
        by
  cbv

theorem fjmidP005RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP005Rounded2563‖ ≤ fjmidP005Radius2563 := by
  rw [fjmidP005Exterior2563]
  norm_num [fjmidP005Rounded2563, fjmidP005Radius2563, fjmidZero2563]

theorem fjmidP005DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  rw [fjmidP005Exterior2563]
  norm_num

noncomputable def fjmidP006Input2563 : RatPair2542 := ((((-1052103689295998182959213518129206281)
    : ℚ) /
        1761648103394083163919587737600000000),
    ((0 : ℚ) /
        1))

def fjmidP006Center2563 : RatPair2542 := (((922862892562499 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def fjmidP006Factor2563 : RatPair2542 := ((((65830361 * 10^40
        + 5132605816725219886317410093330580982241) : ℚ) /
        (903209 * 10^40
        + 4502448949280199772634820186661161964482)),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP006Error2563 : ℝ := ((1217513621385 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem fjmidP006BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP006Center2563‖ ≤ fjmidP006Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP006Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP006Input2563]
  have hc : (compactExp2547 fjmidP006Input2563 7).1 = fjmidP006Center2563 := by cbv
  have he : ((compactExp2547 fjmidP006Input2563 7).2 : ℝ) = fjmidP006Error2563 := by
    have hq : (compactExp2547 fjmidP006Input2563 7).2 =
        ((1217513621385 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by cbv
    rw [hq]
    norm_num [fjmidP006Error2563]
  have h := compactExp_error2547 fjmidP006Input2563 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^7 * embedPair2542 fjmidP006Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP006Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP006DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP006Factor2563 * embedPair2542 fjmidP006Center2563‖ ≤
        (pairMagnitude2542 fjmidP006Factor2563 : ℝ) * fjmidP006Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP006Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP006Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP006BaseError2563
    (embedPair_magnitude2542 fjmidP006Factor2563)

def fjmidP006Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP006Radius2563 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP006RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP006Factor2563 fjmidP006Center2563) = fjmidP006Rounded2563 :=
        by
  cbv

theorem fjmidP006RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP006Rounded2563‖ ≤ fjmidP006Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP006Factor2563 fjmidP006Center2563)
  rw [fjmidP006RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP006Factor2563 * embedPair2542 fjmidP006Center2563)
    (embedPair2542 fjmidP006Rounded2563)).trans (add_le_add fjmidP006DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP006Factor2563, fjmidP006Error2563, rounding2542,
      fjmidP006Radius2563]

theorem fjmidP006DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP006Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP006RoundedError2563 (embedPair_magnitude2542
      fjmidP006Rounded2563))
  apply h'.trans
  norm_num [fjmidP006Radius2563, pairMagnitude2542, fjmidP006Rounded2563]

noncomputable def fjmidP007Input2563 : RatPair2542 := ((((-((7224110 * 10^40
        + 4406628376595866370136231705353501324162) * 10^40
        + 1511332573809066646429207955160645591911)) : ℚ) /
        ((9965107 * 10^40
        + 8381342301379574219443224222204798749052) * 10^40
        + 4506946462156526889793870220492800000000)),
    ((0 : ℚ) /
        1))

def fjmidP007Center2563 : RatPair2542 := (((10355918689374196829550765419 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def fjmidP007Factor2563 : RatPair2542 := ((((((171489622156943000195426447198 * 10^40
        + 6062598187743684290659208420886884284629) * 10^40
        + 1535621732405997006189222369556390501971) * 10^40
        + 5719713847345472865924858164472905824001) : ℚ) /
        (((11560434268978921445520672852 * 10^40
        + 3151491610707945740034502288795420775469) * 10^40
        + 9342842308133684351566010846049001848136) * 10^40
        + 2052163694690945731849716328945811648002)),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP007Error2563 : ℝ := ((1504548178364114737319599 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP007BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP007Center2563‖ ≤ fjmidP007Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP007Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP007Input2563]
  have hc : (compactExp2547 fjmidP007Input2563 6).1 = fjmidP007Center2563 := by cbv
  have he : ((compactExp2547 fjmidP007Input2563 6).2 : ℝ) = fjmidP007Error2563 := by
    have hq : (compactExp2547 fjmidP007Input2563 6).2 =
        ((1504548178364114737319599 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP007Error2563]
  have h := compactExp_error2547 fjmidP007Input2563 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^6 * embedPair2542 fjmidP007Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP007Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP007DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP007Factor2563 * embedPair2542 fjmidP007Center2563‖ ≤
        (pairMagnitude2542 fjmidP007Factor2563 : ℝ) * fjmidP007Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP007Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP007Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP007BaseError2563
    (embedPair_magnitude2542 fjmidP007Factor2563)

def fjmidP007Rounded2563 : RatPair2542 :=
  (((66622755513 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP007Radius2563 : ℝ := ((2199042613979 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP007RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP007Factor2563 fjmidP007Center2563) = fjmidP007Rounded2563 :=
        by
  cbv

theorem fjmidP007RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP007Rounded2563‖ ≤ fjmidP007Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP007Factor2563 fjmidP007Center2563)
  rw [fjmidP007RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP007Factor2563 * embedPair2542 fjmidP007Center2563)
    (embedPair2542 fjmidP007Rounded2563)).trans (add_le_add fjmidP007DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP007Factor2563, fjmidP007Error2563, rounding2542,
      fjmidP007Radius2563]

theorem fjmidP007DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP007Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP007RoundedError2563 (embedPair_magnitude2542
      fjmidP007Rounded2563))
  apply h'.trans
  norm_num [fjmidP007Radius2563, pairMagnitude2542, fjmidP007Rounded2563]

noncomputable def fjmidP008Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1261719220645415482412484183 : ℚ) /
        3777893186295716170956800000000))

def fjmidP008Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP008Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3978571430081297) : ℚ) /
        281474976710656))

noncomputable def fjmidP008Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP008BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP008Center2563‖ ≤ fjmidP008Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP008Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP008Input2563]
  have hc : (compactExp2547 fjmidP008Input2563 17).1 = fjmidP008Center2563 := by cbv
  have he : ((compactExp2547 fjmidP008Input2563 17).2 : ℝ) = fjmidP008Error2563 := by
    have hq : (compactExp2547 fjmidP008Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP008Error2563]
  have h := compactExp_error2547 fjmidP008Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP008Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP008Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP008DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP008Factor2563 * embedPair2542 fjmidP008Center2563‖ ≤
        (pairMagnitude2542 fjmidP008Factor2563 : ℝ) * fjmidP008Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP008Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP008Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP008BaseError2563
    (embedPair_magnitude2542 fjmidP008Factor2563)

def fjmidP008Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP008Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP008RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP008Factor2563 fjmidP008Center2563) = fjmidP008Rounded2563 :=
        by
  cbv

theorem fjmidP008RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP008Rounded2563‖ ≤ fjmidP008Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP008Factor2563 fjmidP008Center2563)
  rw [fjmidP008RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP008Factor2563 * embedPair2542 fjmidP008Center2563)
    (embedPair2542 fjmidP008Rounded2563)).trans (add_le_add fjmidP008DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP008Factor2563, fjmidP008Error2563, rounding2542,
      fjmidP008Radius2563]

theorem fjmidP008DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP008Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP008RoundedError2563 (embedPair_magnitude2542
      fjmidP008Rounded2563))
  apply h'.trans
  norm_num [fjmidP008Radius2563, pairMagnitude2542, fjmidP008Rounded2563]

noncomputable def fjmidP009Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1876507056447276098253971529 : ℚ) /
        3777893186295716170956800000000))

def fjmidP009Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP009Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-5917178117733711) : ℚ) /
        281474976710656))

noncomputable def fjmidP009Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP009BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP009Center2563‖ ≤ fjmidP009Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP009Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP009Input2563]
  have hc : (compactExp2547 fjmidP009Input2563 17).1 = fjmidP009Center2563 := by cbv
  have he : ((compactExp2547 fjmidP009Input2563 17).2 : ℝ) = fjmidP009Error2563 := by
    have hq : (compactExp2547 fjmidP009Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP009Error2563]
  have h := compactExp_error2547 fjmidP009Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP009Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP009Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP009DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP009Factor2563 * embedPair2542 fjmidP009Center2563‖ ≤
        (pairMagnitude2542 fjmidP009Factor2563 : ℝ) * fjmidP009Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP009Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP009Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP009BaseError2563
    (embedPair_magnitude2542 fjmidP009Factor2563)

def fjmidP009Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP009Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP009RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP009Factor2563 fjmidP009Center2563) = fjmidP009Rounded2563 :=
        by
  cbv

theorem fjmidP009RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP009Rounded2563‖ ≤ fjmidP009Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP009Factor2563 fjmidP009Center2563)
  rw [fjmidP009RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP009Factor2563 * embedPair2542 fjmidP009Center2563)
    (embedPair2542 fjmidP009Rounded2563)).trans (add_le_add fjmidP009DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP009Factor2563, fjmidP009Error2563, rounding2542,
      fjmidP009Radius2563]

theorem fjmidP009DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP009Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP009RoundedError2563 (embedPair_magnitude2542
      fjmidP009Rounded2563))
  apply h'.trans
  norm_num [fjmidP009Radius2563, pairMagnitude2542, fjmidP009Rounded2563]

noncomputable def fjmidP010Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1116282043593459096767143119 : ℚ) /
        1888946593147858085478400000000))

def fjmidP010Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP010Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3519965277442521) : ℚ) /
        140737488355328))

noncomputable def fjmidP010Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP010BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP010Center2563‖ ≤ fjmidP010Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP010Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP010Input2563]
  have hc : (compactExp2547 fjmidP010Input2563 17).1 = fjmidP010Center2563 := by cbv
  have he : ((compactExp2547 fjmidP010Input2563 17).2 : ℝ) = fjmidP010Error2563 := by
    have hq : (compactExp2547 fjmidP010Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP010Error2563]
  have h := compactExp_error2547 fjmidP010Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP010Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP010Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP010DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP010Factor2563 * embedPair2542 fjmidP010Center2563‖ ≤
        (pairMagnitude2542 fjmidP010Factor2563 : ℝ) * fjmidP010Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP010Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP010Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP010BaseError2563
    (embedPair_magnitude2542 fjmidP010Factor2563)

def fjmidP010Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP010Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP010RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP010Factor2563 fjmidP010Center2563) = fjmidP010Rounded2563 :=
        by
  cbv

theorem fjmidP010RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP010Rounded2563‖ ≤ fjmidP010Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP010Factor2563 fjmidP010Center2563)
  rw [fjmidP010RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP010Factor2563 * embedPair2542 fjmidP010Center2563)
    (embedPair2542 fjmidP010Rounded2563)).trans (add_le_add fjmidP010DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP010Factor2563, fjmidP010Error2563, rounding2542,
      fjmidP010Radius2563]

theorem fjmidP010DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP010Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP010RoundedError2563 (embedPair_magnitude2542
      fjmidP010Rounded2563))
  apply h'.trans
  norm_num [fjmidP010Radius2563, pairMagnitude2542, fjmidP010Rounded2563]

noncomputable def fjmidP011Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1234978985119947335660559039 : ℚ) /
        1888946593147858085478400000000))

def fjmidP011Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP011Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3894251610461801) : ℚ) /
        140737488355328))

noncomputable def fjmidP011Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP011BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP011Center2563‖ ≤ fjmidP011Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP011Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP011Input2563]
  have hc : (compactExp2547 fjmidP011Input2563 17).1 = fjmidP011Center2563 := by cbv
  have he : ((compactExp2547 fjmidP011Input2563 17).2 : ℝ) = fjmidP011Error2563 := by
    have hq : (compactExp2547 fjmidP011Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP011Error2563]
  have h := compactExp_error2547 fjmidP011Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP011Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP011Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP011DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP011Factor2563 * embedPair2542 fjmidP011Center2563‖ ≤
        (pairMagnitude2542 fjmidP011Factor2563 : ℝ) * fjmidP011Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP011Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP011Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP011BaseError2563
    (embedPair_magnitude2542 fjmidP011Factor2563)

def fjmidP011Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP011Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP011RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP011Factor2563 fjmidP011Center2563) = fjmidP011Rounded2563 :=
        by
  cbv

theorem fjmidP011RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP011Rounded2563‖ ≤ fjmidP011Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP011Factor2563 fjmidP011Center2563)
  rw [fjmidP011RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP011Factor2563 * embedPair2542 fjmidP011Center2563)
    (embedPair2542 fjmidP011Rounded2563)).trans (add_le_add fjmidP011DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP011Factor2563, fjmidP011Error2563, rounding2542,
      fjmidP011Radius2563]

theorem fjmidP011DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP011Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP011RoundedError2563 (embedPair_magnitude2542
      fjmidP011Rounded2563))
  apply h'.trans
  norm_num [fjmidP011Radius2563, pairMagnitude2542, fjmidP011Rounded2563]

noncomputable def fjmidP012Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((27158399338384035222570051 : ℚ) /
        37778931862957161709568000000))

def fjmidP012Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP012Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-2140960324737725) : ℚ) /
        70368744177664))

noncomputable def fjmidP012Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP012BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP012Center2563‖ ≤ fjmidP012Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP012Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP012Input2563]
  have hc : (compactExp2547 fjmidP012Input2563 17).1 = fjmidP012Center2563 := by cbv
  have he : ((compactExp2547 fjmidP012Input2563 17).2 : ℝ) = fjmidP012Error2563 := by
    have hq : (compactExp2547 fjmidP012Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP012Error2563]
  have h := compactExp_error2547 fjmidP012Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP012Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP012Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP012DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP012Factor2563 * embedPair2542 fjmidP012Center2563‖ ≤
        (pairMagnitude2542 fjmidP012Factor2563 : ℝ) * fjmidP012Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP012Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP012Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP012BaseError2563
    (embedPair_magnitude2542 fjmidP012Factor2563)

def fjmidP012Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP012Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP012RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP012Factor2563 fjmidP012Center2563) = fjmidP012Rounded2563 :=
        by
  cbv

theorem fjmidP012RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP012Rounded2563‖ ≤ fjmidP012Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP012Factor2563 fjmidP012Center2563)
  rw [fjmidP012RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP012Factor2563 * embedPair2542 fjmidP012Center2563)
    (embedPair2542 fjmidP012Rounded2563)).trans (add_le_add fjmidP012DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP012Factor2563, fjmidP012Error2563, rounding2542,
      fjmidP012Radius2563]

theorem fjmidP012DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP012Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP012RoundedError2563 (embedPair_magnitude2542
      fjmidP012Rounded2563))
  apply h'.trans
  norm_num [fjmidP012Radius2563, pairMagnitude2542, fjmidP012Rounded2563]

noncomputable def fjmidP013Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((293990861666597709724015149 : ℚ) /
        377789318629571617095680000000))

def fjmidP013Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP013Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-4635197846686455) : ℚ) /
        140737488355328))

noncomputable def fjmidP013Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP013BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP013Center2563‖ ≤ fjmidP013Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP013Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP013Input2563]
  have hc : (compactExp2547 fjmidP013Input2563 17).1 = fjmidP013Center2563 := by cbv
  have he : ((compactExp2547 fjmidP013Input2563 17).2 : ℝ) = fjmidP013Error2563 := by
    have hq : (compactExp2547 fjmidP013Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP013Error2563]
  have h := compactExp_error2547 fjmidP013Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP013Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP013Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP013DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP013Factor2563 * embedPair2542 fjmidP013Center2563‖ ≤
        (pairMagnitude2542 fjmidP013Factor2563 : ℝ) * fjmidP013Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP013Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP013Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP013BaseError2563
    (embedPair_magnitude2542 fjmidP013Factor2563)

def fjmidP013Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP013Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP013RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP013Factor2563 fjmidP013Center2563) = fjmidP013Rounded2563 :=
        by
  cbv

theorem fjmidP013RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP013Rounded2563‖ ≤ fjmidP013Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP013Factor2563 fjmidP013Center2563)
  rw [fjmidP013RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP013Factor2563 * embedPair2542 fjmidP013Center2563)
    (embedPair2542 fjmidP013Rounded2563)).trans (add_le_add fjmidP013DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP013Factor2563, fjmidP013Error2563, rounding2542,
      fjmidP013Radius2563]

theorem fjmidP013DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP013Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP013RoundedError2563 (embedPair_magnitude2542
      fjmidP013Rounded2563))
  apply h'.trans
  norm_num [fjmidP013Radius2563, pairMagnitude2542, fjmidP013Rounded2563]

noncomputable def fjmidP014Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1677542468568059149194008229 : ℚ) /
        1888946593147858085478400000000))

def fjmidP014Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP014Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-5289784310949011) : ℚ) /
        140737488355328))

noncomputable def fjmidP014Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP014BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP014Center2563‖ ≤ fjmidP014Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP014Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP014Input2563]
  have hc : (compactExp2547 fjmidP014Input2563 17).1 = fjmidP014Center2563 := by cbv
  have he : ((compactExp2547 fjmidP014Input2563 17).2 : ℝ) = fjmidP014Error2563 := by
    have hq : (compactExp2547 fjmidP014Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP014Error2563]
  have h := compactExp_error2547 fjmidP014Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP014Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP014Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP014DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP014Factor2563 * embedPair2542 fjmidP014Center2563‖ ≤
        (pairMagnitude2542 fjmidP014Factor2563 : ℝ) * fjmidP014Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP014Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP014Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP014BaseError2563
    (embedPair_magnitude2542 fjmidP014Factor2563)

def fjmidP014Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP014Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP014RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP014Factor2563 fjmidP014Center2563) = fjmidP014Rounded2563 :=
        by
  cbv

theorem fjmidP014RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP014Rounded2563‖ ≤ fjmidP014Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP014Factor2563 fjmidP014Center2563)
  rw [fjmidP014RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP014Factor2563 * embedPair2542 fjmidP014Center2563)
    (embedPair2542 fjmidP014Rounded2563)).trans (add_le_add fjmidP014DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP014Factor2563, fjmidP014Error2563, rounding2542,
      fjmidP014Radius2563]

theorem fjmidP014DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP014Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP014RoundedError2563 (embedPair_magnitude2542
      fjmidP014Rounded2563))
  apply h'.trans
  norm_num [fjmidP014Radius2563, pairMagnitude2542, fjmidP014Rounded2563]

noncomputable def fjmidP015Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1826280091905607810113908433 : ℚ) /
        1888946593147858085478400000000))

def fjmidP015Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP015Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-5758797740487047) : ℚ) /
        140737488355328))

noncomputable def fjmidP015Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP015BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP015Center2563‖ ≤ fjmidP015Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP015Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP015Input2563]
  have hc : (compactExp2547 fjmidP015Input2563 17).1 = fjmidP015Center2563 := by cbv
  have he : ((compactExp2547 fjmidP015Input2563 17).2 : ℝ) = fjmidP015Error2563 := by
    have hq : (compactExp2547 fjmidP015Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP015Error2563]
  have h := compactExp_error2547 fjmidP015Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP015Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP015Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP015DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP015Factor2563 * embedPair2542 fjmidP015Center2563‖ ≤
        (pairMagnitude2542 fjmidP015Factor2563 : ℝ) * fjmidP015Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP015Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP015Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP015BaseError2563
    (embedPair_magnitude2542 fjmidP015Factor2563)

def fjmidP015Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP015Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP015RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP015Factor2563 fjmidP015Center2563) = fjmidP015Rounded2563 :=
        by
  cbv

theorem fjmidP015RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP015Rounded2563‖ ≤ fjmidP015Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP015Factor2563 fjmidP015Center2563)
  rw [fjmidP015RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP015Factor2563 * embedPair2542 fjmidP015Center2563)
    (embedPair2542 fjmidP015Rounded2563)).trans (add_le_add fjmidP015DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP015Factor2563, fjmidP015Error2563, rounding2542,
      fjmidP015Radius2563]

theorem fjmidP015DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP015Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP015RoundedError2563 (embedPair_magnitude2542
      fjmidP015Rounded2563))
  apply h'.trans
  norm_num [fjmidP015Radius2563, pairMagnitude2542, fjmidP015Rounded2563]

noncomputable def fjmidP016Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((966884756949258260679651951 : ℚ) /
        944473296573929042739200000000))

def fjmidP016Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP016Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3048871735671609) : ℚ) /
        70368744177664))

noncomputable def fjmidP016Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP016BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP016Center2563‖ ≤ fjmidP016Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP016Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP016Input2563]
  have hc : (compactExp2547 fjmidP016Input2563 17).1 = fjmidP016Center2563 := by cbv
  have he : ((compactExp2547 fjmidP016Input2563 17).2 : ℝ) = fjmidP016Error2563 := by
    have hq : (compactExp2547 fjmidP016Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP016Error2563]
  have h := compactExp_error2547 fjmidP016Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP016Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP016Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP016DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP016Factor2563 * embedPair2542 fjmidP016Center2563‖ ≤
        (pairMagnitude2542 fjmidP016Factor2563 : ℝ) * fjmidP016Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP016Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP016Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP016BaseError2563
    (embedPair_magnitude2542 fjmidP016Factor2563)

def fjmidP016Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP016Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP016RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP016Factor2563 fjmidP016Center2563) = fjmidP016Rounded2563 :=
        by
  cbv

theorem fjmidP016RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP016Rounded2563‖ ≤ fjmidP016Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP016Factor2563 fjmidP016Center2563)
  rw [fjmidP016RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP016Factor2563 * embedPair2542 fjmidP016Center2563)
    (embedPair2542 fjmidP016Rounded2563)).trans (add_le_add fjmidP016DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP016Factor2563, fjmidP016Error2563, rounding2542,
      fjmidP016Radius2563]

theorem fjmidP016DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP016Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP016RoundedError2563 (embedPair_magnitude2542
      fjmidP016Rounded2563))
  apply h'.trans
  norm_num [fjmidP016Radius2563, pairMagnitude2542, fjmidP016Rounded2563]

noncomputable def fjmidP017Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2142560996036405154016564653 : ℚ) /
        1888946593147858085478400000000))

def fjmidP017Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP017Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-6756124363134027) : ℚ) /
        140737488355328))

noncomputable def fjmidP017Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP017BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP017Center2563‖ ≤ fjmidP017Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP017Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP017Input2563]
  have hc : (compactExp2547 fjmidP017Input2563 17).1 = fjmidP017Center2563 := by cbv
  have he : ((compactExp2547 fjmidP017Input2563 17).2 : ℝ) = fjmidP017Error2563 := by
    have hq : (compactExp2547 fjmidP017Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP017Error2563]
  have h := compactExp_error2547 fjmidP017Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP017Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP017Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP017DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP017Factor2563 * embedPair2542 fjmidP017Center2563‖ ≤
        (pairMagnitude2542 fjmidP017Factor2563 : ℝ) * fjmidP017Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP017Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP017Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP017BaseError2563
    (embedPair_magnitude2542 fjmidP017Factor2563)

def fjmidP017Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP017Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP017RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP017Factor2563 fjmidP017Center2563) = fjmidP017Rounded2563 :=
        by
  cbv

theorem fjmidP017RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP017Rounded2563‖ ≤ fjmidP017Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP017Factor2563 fjmidP017Center2563)
  rw [fjmidP017RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP017Factor2563 * embedPair2542 fjmidP017Center2563)
    (embedPair2542 fjmidP017Rounded2563)).trans (add_le_add fjmidP017DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP017Factor2563, fjmidP017Error2563, rounding2542,
      fjmidP017Radius2563]

theorem fjmidP017DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP017Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP017RoundedError2563 (embedPair_magnitude2542
      fjmidP017Rounded2563))
  apply h'.trans
  norm_num [fjmidP017Radius2563, pairMagnitude2542, fjmidP017Rounded2563]

noncomputable def fjmidP018Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((555375153147096446436377307 : ℚ) /
        472236648286964521369600000000))

def fjmidP018Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP018Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-1751261042181613) : ℚ) /
        35184372088832))

noncomputable def fjmidP018Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP018BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP018Center2563‖ ≤ fjmidP018Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP018Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP018Input2563]
  have hc : (compactExp2547 fjmidP018Input2563 17).1 = fjmidP018Center2563 := by cbv
  have he : ((compactExp2547 fjmidP018Input2563 17).2 : ℝ) = fjmidP018Error2563 := by
    have hq : (compactExp2547 fjmidP018Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP018Error2563]
  have h := compactExp_error2547 fjmidP018Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP018Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP018Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP018DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP018Factor2563 * embedPair2542 fjmidP018Center2563‖ ≤
        (pairMagnitude2542 fjmidP018Factor2563 : ℝ) * fjmidP018Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP018Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP018Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP018BaseError2563
    (embedPair_magnitude2542 fjmidP018Factor2563)

def fjmidP018Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP018Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP018RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP018Factor2563 fjmidP018Center2563) = fjmidP018Rounded2563 :=
        by
  cbv

theorem fjmidP018RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP018Rounded2563‖ ≤ fjmidP018Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP018Factor2563 fjmidP018Center2563)
  rw [fjmidP018RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP018Factor2563 * embedPair2542 fjmidP018Center2563)
    (embedPair2542 fjmidP018Rounded2563)).trans (add_le_add fjmidP018DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP018Factor2563, fjmidP018Error2563, rounding2542,
      fjmidP018Radius2563]

theorem fjmidP018DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP018Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP018RoundedError2563 (embedPair_magnitude2542
      fjmidP018Rounded2563))
  apply h'.trans
  norm_num [fjmidP018Radius2563, pairMagnitude2542, fjmidP018Rounded2563]

noncomputable def fjmidP019Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((118208299174604243670929049 : ℚ) /
        94447329657392904273920000000))

def fjmidP019Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP019Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-1863727500536955) : ℚ) /
        35184372088832))

noncomputable def fjmidP019Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP019BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP019Center2563‖ ≤ fjmidP019Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP019Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP019Input2563]
  have hc : (compactExp2547 fjmidP019Input2563 17).1 = fjmidP019Center2563 := by cbv
  have he : ((compactExp2547 fjmidP019Input2563 17).2 : ℝ) = fjmidP019Error2563 := by
    have hq : (compactExp2547 fjmidP019Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP019Error2563]
  have h := compactExp_error2547 fjmidP019Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP019Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP019Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP019DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP019Factor2563 * embedPair2542 fjmidP019Center2563‖ ≤
        (pairMagnitude2542 fjmidP019Factor2563 : ℝ) * fjmidP019Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP019Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP019Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP019BaseError2563
    (embedPair_magnitude2542 fjmidP019Factor2563)

def fjmidP019Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP019Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP019RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP019Factor2563 fjmidP019Center2563) = fjmidP019Rounded2563 :=
        by
  cbv

theorem fjmidP019RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP019Rounded2563‖ ≤ fjmidP019Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP019Factor2563 fjmidP019Center2563)
  rw [fjmidP019RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP019Factor2563 * embedPair2542 fjmidP019Center2563)
    (embedPair2542 fjmidP019Rounded2563)).trans (add_le_add fjmidP019DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP019Factor2563, fjmidP019Error2563, rounding2542,
      fjmidP019Radius2563]

theorem fjmidP019DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP019Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP019RoundedError2563 (embedPair_magnitude2542
      fjmidP019Rounded2563))
  apply h'.trans
  norm_num [fjmidP019Radius2563, pairMagnitude2542, fjmidP019Rounded2563]

noncomputable def fjmidP020Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2519303167856168777929316541 : ℚ) /
        1888946593147858085478400000000))

def fjmidP020Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP020Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-7944103127967419) : ℚ) /
        140737488355328))

noncomputable def fjmidP020Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP020BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP020Center2563‖ ≤ fjmidP020Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP020Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP020Input2563]
  have hc : (compactExp2547 fjmidP020Input2563 17).1 = fjmidP020Center2563 := by cbv
  have he : ((compactExp2547 fjmidP020Input2563 17).2 : ℝ) = fjmidP020Error2563 := by
    have hq : (compactExp2547 fjmidP020Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP020Error2563]
  have h := compactExp_error2547 fjmidP020Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP020Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP020Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP020DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP020Factor2563 * embedPair2542 fjmidP020Center2563‖ ≤
        (pairMagnitude2542 fjmidP020Factor2563 : ℝ) * fjmidP020Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP020Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP020Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP020BaseError2563
    (embedPair_magnitude2542 fjmidP020Factor2563)

def fjmidP020Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP020Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP020RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP020Factor2563 fjmidP020Center2563) = fjmidP020Rounded2563 :=
        by
  cbv

theorem fjmidP020RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP020Rounded2563‖ ≤ fjmidP020Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP020Factor2563 fjmidP020Center2563)
  rw [fjmidP020RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP020Factor2563 * embedPair2542 fjmidP020Center2563)
    (embedPair2542 fjmidP020Rounded2563)).trans (add_le_add fjmidP020DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP020Factor2563, fjmidP020Error2563, rounding2542,
      fjmidP020Radius2563]

theorem fjmidP020DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP020Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP020RoundedError2563 (embedPair_magnitude2542
      fjmidP020Rounded2563))
  apply h'.trans
  norm_num [fjmidP020Radius2563, pairMagnitude2542, fjmidP020Rounded2563]

noncomputable def fjmidP021Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2648771212589104536068841693 : ℚ) /
        1888946593147858085478400000000))

def fjmidP021Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP021Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-8352353914239387) : ℚ) /
        140737488355328))

noncomputable def fjmidP021Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP021BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP021Center2563‖ ≤ fjmidP021Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP021Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP021Input2563]
  have hc : (compactExp2547 fjmidP021Input2563 17).1 = fjmidP021Center2563 := by cbv
  have he : ((compactExp2547 fjmidP021Input2563 17).2 : ℝ) = fjmidP021Error2563 := by
    have hq : (compactExp2547 fjmidP021Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP021Error2563]
  have h := compactExp_error2547 fjmidP021Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP021Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP021Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP021DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP021Factor2563 * embedPair2542 fjmidP021Center2563‖ ≤
        (pairMagnitude2542 fjmidP021Factor2563 : ℝ) * fjmidP021Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP021Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP021Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP021BaseError2563
    (embedPair_magnitude2542 fjmidP021Factor2563)

def fjmidP021Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP021Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP021RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP021Factor2563 fjmidP021Center2563) = fjmidP021Rounded2563 :=
        by
  cbv

theorem fjmidP021RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP021Rounded2563‖ ≤ fjmidP021Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP021Factor2563 fjmidP021Center2563)
  rw [fjmidP021RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP021Factor2563 * embedPair2542 fjmidP021Center2563)
    (embedPair2542 fjmidP021Rounded2563)).trans (add_le_add fjmidP021DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP021Factor2563, fjmidP021Error2563, rounding2542,
      fjmidP021Radius2563]

theorem fjmidP021DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP021Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP021RoundedError2563 (embedPair_magnitude2542
      fjmidP021Rounded2563))
  apply h'.trans
  norm_num [fjmidP021Radius2563, pairMagnitude2542, fjmidP021Rounded2563]

noncomputable def fjmidP022Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((543007546456794340281131487 : ℚ) /
        377789318629571617095680000000))

def fjmidP022Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP022Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-8561311721741165) : ℚ) /
        140737488355328))

noncomputable def fjmidP022Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP022BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP022Center2563‖ ≤ fjmidP022Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP022Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP022Input2563]
  have hc : (compactExp2547 fjmidP022Input2563 17).1 = fjmidP022Center2563 := by cbv
  have he : ((compactExp2547 fjmidP022Input2563 17).2 : ℝ) = fjmidP022Error2563 := by
    have hq : (compactExp2547 fjmidP022Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP022Error2563]
  have h := compactExp_error2547 fjmidP022Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP022Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP022Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP022DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP022Factor2563 * embedPair2542 fjmidP022Center2563‖ ≤
        (pairMagnitude2542 fjmidP022Factor2563 : ℝ) * fjmidP022Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP022Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP022Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP022BaseError2563
    (embedPair_magnitude2542 fjmidP022Factor2563)

def fjmidP022Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP022Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP022RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP022Factor2563 fjmidP022Center2563) = fjmidP022Rounded2563 :=
        by
  cbv

theorem fjmidP022RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP022Rounded2563‖ ≤ fjmidP022Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP022Factor2563 fjmidP022Center2563)
  rw [fjmidP022RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP022Factor2563 * embedPair2542 fjmidP022Center2563)
    (embedPair2542 fjmidP022Rounded2563)).trans (add_le_add fjmidP022DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP022Factor2563, fjmidP022Error2563, rounding2542,
      fjmidP022Radius2563]

theorem fjmidP022DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP022Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP022RoundedError2563 (embedPair_magnitude2542
      fjmidP022Rounded2563))
  apply h'.trans
  norm_num [fjmidP022Radius2563, pairMagnitude2542, fjmidP022Rounded2563]

noncomputable def fjmidP023Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1453048211174897778209007387 : ℚ) /
        944473296573929042739200000000))

def fjmidP023Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP023Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-4581887954876333) : ℚ) /
        70368744177664))

noncomputable def fjmidP023Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP023BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP023Center2563‖ ≤ fjmidP023Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP023Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP023Input2563]
  have hc : (compactExp2547 fjmidP023Input2563 17).1 = fjmidP023Center2563 := by cbv
  have he : ((compactExp2547 fjmidP023Input2563 17).2 : ℝ) = fjmidP023Error2563 := by
    have hq : (compactExp2547 fjmidP023Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP023Error2563]
  have h := compactExp_error2547 fjmidP023Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP023Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP023Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP023DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP023Factor2563 * embedPair2542 fjmidP023Center2563‖ ≤
        (pairMagnitude2542 fjmidP023Factor2563 : ℝ) * fjmidP023Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP023Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP023Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP023BaseError2563
    (embedPair_magnitude2542 fjmidP023Factor2563)

def fjmidP023Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP023Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP023RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP023Factor2563 fjmidP023Center2563) = fjmidP023Rounded2563 :=
        by
  cbv

theorem fjmidP023RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP023Rounded2563‖ ≤ fjmidP023Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP023Factor2563 fjmidP023Center2563)
  rw [fjmidP023RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP023Factor2563 * embedPair2542 fjmidP023Center2563)
    (embedPair2542 fjmidP023Rounded2563)).trans (add_le_add fjmidP023DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP023Factor2563, fjmidP023Error2563, rounding2542,
      fjmidP023Radius2563]

theorem fjmidP023DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP023Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP023RoundedError2563 (embedPair_magnitude2542
      fjmidP023Rounded2563))
  apply h'.trans
  norm_num [fjmidP023Radius2563, pairMagnitude2542, fjmidP023Rounded2563]

noncomputable def fjmidP024Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1496949629611413064555803333 : ℚ) /
        944473296573929042739200000000))

def fjmidP024Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP024Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-4720322026636147) : ℚ) /
        70368744177664))

noncomputable def fjmidP024Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP024BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP024Center2563‖ ≤ fjmidP024Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP024Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP024Input2563]
  have hc : (compactExp2547 fjmidP024Input2563 17).1 = fjmidP024Center2563 := by cbv
  have he : ((compactExp2547 fjmidP024Input2563 17).2 : ℝ) = fjmidP024Error2563 := by
    have hq : (compactExp2547 fjmidP024Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP024Error2563]
  have h := compactExp_error2547 fjmidP024Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP024Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP024Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP024DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP024Factor2563 * embedPair2542 fjmidP024Center2563‖ ≤
        (pairMagnitude2542 fjmidP024Factor2563 : ℝ) * fjmidP024Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP024Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP024Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP024BaseError2563
    (embedPair_magnitude2542 fjmidP024Factor2563)

def fjmidP024Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP024Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP024RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP024Factor2563 fjmidP024Center2563) = fjmidP024Rounded2563 :=
        by
  cbv

theorem fjmidP024RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP024Rounded2563‖ ≤ fjmidP024Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP024Factor2563 fjmidP024Center2563)
  rw [fjmidP024RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP024Factor2563 * embedPair2542 fjmidP024Center2563)
    (embedPair2542 fjmidP024Rounded2563)).trans (add_le_add fjmidP024DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP024Factor2563, fjmidP024Error2563, rounding2542,
      fjmidP024Radius2563]

theorem fjmidP024DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP024Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP024RoundedError2563 (embedPair_magnitude2542
      fjmidP024Rounded2563))
  apply h'.trans
  norm_num [fjmidP024Radius2563, pairMagnitude2542, fjmidP024Rounded2563]

noncomputable def fjmidP025Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((48499811018293309025440887 : ℚ) /
        29514790517935282585600000000))

def fjmidP025Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP025Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-152934154702833) : ℚ) /
        2199023255552))

noncomputable def fjmidP025Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP025BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP025Center2563‖ ≤ fjmidP025Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP025Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP025Input2563]
  have hc : (compactExp2547 fjmidP025Input2563 17).1 = fjmidP025Center2563 := by cbv
  have he : ((compactExp2547 fjmidP025Input2563 17).2 : ℝ) = fjmidP025Error2563 := by
    have hq : (compactExp2547 fjmidP025Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP025Error2563]
  have h := compactExp_error2547 fjmidP025Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP025Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP025Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP025DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP025Factor2563 * embedPair2542 fjmidP025Center2563‖ ≤
        (pairMagnitude2542 fjmidP025Factor2563 : ℝ) * fjmidP025Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP025Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP025Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP025BaseError2563
    (embedPair_magnitude2542 fjmidP025Factor2563)

def fjmidP025Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP025Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP025RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP025Factor2563 fjmidP025Center2563) = fjmidP025Rounded2563 :=
        by
  cbv

theorem fjmidP025RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP025Rounded2563‖ ≤ fjmidP025Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP025Factor2563 fjmidP025Center2563)
  rw [fjmidP025RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP025Factor2563 * embedPair2542 fjmidP025Center2563)
    (embedPair2542 fjmidP025Rounded2563)).trans (add_le_add fjmidP025DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP025Factor2563, fjmidP025Error2563, rounding2542,
      fjmidP025Radius2563]

theorem fjmidP025DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP025Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP025RoundedError2563 (embedPair_magnitude2542
      fjmidP025Rounded2563))
  apply h'.trans
  norm_num [fjmidP025Radius2563, pairMagnitude2542, fjmidP025Rounded2563]

noncomputable def fjmidP026Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((100515438378930241589387643 : ℚ) /
        59029581035870565171200000000))

def fjmidP026Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP026Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-316954711375437) : ℚ) /
        4398046511104))

noncomputable def fjmidP026Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP026BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP026Center2563‖ ≤ fjmidP026Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP026Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP026Input2563]
  have hc : (compactExp2547 fjmidP026Input2563 17).1 = fjmidP026Center2563 := by cbv
  have he : ((compactExp2547 fjmidP026Input2563 17).2 : ℝ) = fjmidP026Error2563 := by
    have hq : (compactExp2547 fjmidP026Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP026Error2563]
  have h := compactExp_error2547 fjmidP026Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP026Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP026Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP026DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP026Factor2563 * embedPair2542 fjmidP026Center2563‖ ≤
        (pairMagnitude2542 fjmidP026Factor2563 : ℝ) * fjmidP026Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP026Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP026Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP026BaseError2563
    (embedPair_magnitude2542 fjmidP026Factor2563)

def fjmidP026Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP026Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP026RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP026Factor2563 fjmidP026Center2563) = fjmidP026Rounded2563 :=
        by
  cbv

theorem fjmidP026RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP026Rounded2563‖ ≤ fjmidP026Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP026Factor2563 fjmidP026Center2563)
  rw [fjmidP026RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP026Factor2563 * embedPair2542 fjmidP026Center2563)
    (embedPair2542 fjmidP026Rounded2563)).trans (add_le_add fjmidP026DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP026Factor2563, fjmidP026Error2563, rounding2542,
      fjmidP026Radius2563]

theorem fjmidP026DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP026Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP026RoundedError2563 (embedPair_magnitude2542
      fjmidP026Rounded2563))
  apply h'.trans
  norm_num [fjmidP026Radius2563, pairMagnitude2542, fjmidP026Rounded2563]

noncomputable def fjmidP027Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((211177751933296260595876053 : ℚ) /
        118059162071741130342400000000))

def fjmidP027Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP027Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-665905501606627) : ℚ) /
        8796093022208))

noncomputable def fjmidP027Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP027BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP027Center2563‖ ≤ fjmidP027Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP027Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP027Input2563]
  have hc : (compactExp2547 fjmidP027Input2563 17).1 = fjmidP027Center2563 := by cbv
  have he : ((compactExp2547 fjmidP027Input2563 17).2 : ℝ) = fjmidP027Error2563 := by
    have hq : (compactExp2547 fjmidP027Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP027Error2563]
  have h := compactExp_error2547 fjmidP027Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP027Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP027Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP027DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP027Factor2563 * embedPair2542 fjmidP027Center2563‖ ≤
        (pairMagnitude2542 fjmidP027Factor2563 : ℝ) * fjmidP027Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP027Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP027Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP027BaseError2563
    (embedPair_magnitude2542 fjmidP027Factor2563)

def fjmidP027Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP027Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP027RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP027Factor2563 fjmidP027Center2563) = fjmidP027Rounded2563 :=
        by
  cbv

theorem fjmidP027RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP027Rounded2563‖ ≤ fjmidP027Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP027Factor2563 fjmidP027Center2563)
  rw [fjmidP027RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP027Factor2563 * embedPair2542 fjmidP027Center2563)
    (embedPair2542 fjmidP027Rounded2563)).trans (add_le_add fjmidP027DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP027Factor2563, fjmidP027Error2563, rounding2542,
      fjmidP027Radius2563]

theorem fjmidP027DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP027Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP027RoundedError2563 (embedPair_magnitude2542
      fjmidP027Rounded2563))
  apply h'.trans
  norm_num [fjmidP027Radius2563, pairMagnitude2542, fjmidP027Rounded2563]

noncomputable def fjmidP028Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((860780157665754287223049953 : ℚ) /
        472236648286964521369600000000))

def fjmidP028Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP028Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-2714292757716727) : ℚ) /
        35184372088832))

noncomputable def fjmidP028Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP028BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP028Center2563‖ ≤ fjmidP028Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP028Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP028Input2563]
  have hc : (compactExp2547 fjmidP028Input2563 17).1 = fjmidP028Center2563 := by cbv
  have he : ((compactExp2547 fjmidP028Input2563 17).2 : ℝ) = fjmidP028Error2563 := by
    have hq : (compactExp2547 fjmidP028Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP028Error2563]
  have h := compactExp_error2547 fjmidP028Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP028Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP028Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP028DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP028Factor2563 * embedPair2542 fjmidP028Center2563‖ ≤
        (pairMagnitude2542 fjmidP028Factor2563 : ℝ) * fjmidP028Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP028Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP028Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP028BaseError2563
    (embedPair_magnitude2542 fjmidP028Factor2563)

def fjmidP028Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP028Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP028RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP028Factor2563 fjmidP028Center2563) = fjmidP028Rounded2563 :=
        by
  cbv

theorem fjmidP028RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP028Rounded2563‖ ≤ fjmidP028Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP028Factor2563 fjmidP028Center2563)
  rw [fjmidP028RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP028Factor2563 * embedPair2542 fjmidP028Center2563)
    (embedPair2542 fjmidP028Rounded2563)).trans (add_le_add fjmidP028DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP028Factor2563, fjmidP028Error2563, rounding2542,
      fjmidP028Radius2563]

theorem fjmidP028DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP028Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP028RoundedError2563 (embedPair_magnitude2542
      fjmidP028Rounded2563))
  apply h'.trans
  norm_num [fjmidP028Radius2563, pairMagnitude2542, fjmidP028Rounded2563]

noncomputable def fjmidP029Input2563 : RatPair2542 := ((((-((2312865 * 10^40
        + 2146202435957712102129842483917578410111) * 10^40
        + 4883202856058925867669125359945801841911)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((885244406725664293840781901 : ℚ) /
        472236648286964521369600000000))

def fjmidP029Center2563 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjmidP029Factor2563 : RatPair2542 := ((((((54884017178483696463843476644 * 10^40
        + 3898147926987883407731067498735338895921) * 10^40
        + 9215765718423453974090306379227006153950) * 10^40
        + 6214940542152917628175240386152593324001) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-2791435723263659) : ℚ) /
        35184372088832))

noncomputable def fjmidP029Error2563 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjmidP029BaseError2563 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP029Center2563‖ ≤ fjmidP029Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjmidP029Input2563‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjmidP029Input2563]
  have hc : (compactExp2547 fjmidP029Input2563 17).1 = fjmidP029Center2563 := by cbv
  have he : ((compactExp2547 fjmidP029Input2563 17).2 : ℝ) = fjmidP029Error2563 := by
    have hq : (compactExp2547 fjmidP029Input2563 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjmidP029Error2563]
  have h := compactExp_error2547 fjmidP029Input2563 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjmidP029Input2563) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjmidP029Input2563, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjmidP029DerivativeError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjmidP029Factor2563 * embedPair2542 fjmidP029Center2563‖ ≤
        (pairMagnitude2542 fjmidP029Factor2563 : ℝ) * fjmidP029Error2563 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (1/2)
      (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjmidP029Factor2563 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjmidP029Factor2563, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjmidP029BaseError2563
    (embedPair_magnitude2542 fjmidP029Factor2563)

def fjmidP029Rounded2563 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjmidP029Radius2563 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjmidP029RoundCompute2563 :
    pairRound2542 (pairMul2542 fjmidP029Factor2563 fjmidP029Center2563) = fjmidP029Rounded2563 :=
        by
  cbv

theorem fjmidP029RoundedError2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjmidP029Rounded2563‖ ≤ fjmidP029Radius2563 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjmidP029Factor2563 fjmidP029Center2563)
  rw [fjmidP029RoundCompute2563, embedPair_mul2542] at hr
  have h := (firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP029Factor2563 * embedPair2542 fjmidP029Center2563)
    (embedPair2542 fjmidP029Rounded2563)).trans (add_le_add fjmidP029DerivativeError2563 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjmidP029Factor2563, fjmidP029Error2563, rounding2542,
      fjmidP029Radius2563]

theorem fjmidP029DerivativeNorm2563 :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpoint_triangle2563
    (weightedUnitJet2539 1 (1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjmidP029Rounded2563) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjmidP029RoundedError2563 (embedPair_magnitude2542
      fjmidP029Rounded2563))
  apply h'.trans
  norm_num [fjmidP029Radius2563, pairMagnitude2542, fjmidP029Rounded2563]

noncomputable def fjmidValue2563 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 fjmidP000Rounded2563
  | 1 => embedPair2542 fjmidP001Rounded2563
  | 2 => embedPair2542 fjmidP002Rounded2563
  | 3 => embedPair2542 fjmidP003Rounded2563
  | 4 => embedPair2542 fjmidP004Rounded2563
  | 5 => embedPair2542 fjmidP005Rounded2563
  | 6 => embedPair2542 fjmidP006Rounded2563
  | 7 => embedPair2542 fjmidP007Rounded2563
  | 8 => embedPair2542 fjmidP008Rounded2563
  | 9 => embedPair2542 fjmidP009Rounded2563
  | 10 => embedPair2542 fjmidP010Rounded2563
  | 11 => embedPair2542 fjmidP011Rounded2563
  | 12 => embedPair2542 fjmidP012Rounded2563
  | 13 => embedPair2542 fjmidP013Rounded2563
  | 14 => embedPair2542 fjmidP014Rounded2563
  | 15 => embedPair2542 fjmidP015Rounded2563
  | 16 => embedPair2542 fjmidP016Rounded2563
  | 17 => embedPair2542 fjmidP017Rounded2563
  | 18 => embedPair2542 fjmidP018Rounded2563
  | 19 => embedPair2542 fjmidP019Rounded2563
  | 20 => embedPair2542 fjmidP020Rounded2563
  | 21 => embedPair2542 fjmidP021Rounded2563
  | 22 => embedPair2542 fjmidP022Rounded2563
  | 23 => embedPair2542 fjmidP023Rounded2563
  | 24 => embedPair2542 fjmidP024Rounded2563
  | 25 => embedPair2542 fjmidP025Rounded2563
  | 26 => embedPair2542 fjmidP026Rounded2563
  | 27 => embedPair2542 fjmidP027Rounded2563
  | 28 => embedPair2542 fjmidP028Rounded2563
  | 29 => embedPair2542 fjmidP029Rounded2563
  | _ => 0

noncomputable def fjmidError2563 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => fjmidP000Radius2563
  | 1 => fjmidP001Radius2563
  | 2 => fjmidP002Radius2563
  | 3 => fjmidP003Radius2563
  | 4 => fjmidP004Radius2563
  | 5 => fjmidP005Radius2563
  | 6 => fjmidP006Radius2563
  | 7 => fjmidP007Radius2563
  | 8 => fjmidP008Radius2563
  | 9 => fjmidP009Radius2563
  | 10 => fjmidP010Radius2563
  | 11 => fjmidP011Radius2563
  | 12 => fjmidP012Radius2563
  | 13 => fjmidP013Radius2563
  | 14 => fjmidP014Radius2563
  | 15 => fjmidP015Radius2563
  | 16 => fjmidP016Radius2563
  | 17 => fjmidP017Radius2563
  | 18 => fjmidP018Radius2563
  | 19 => fjmidP019Radius2563
  | 20 => fjmidP020Radius2563
  | 21 => fjmidP021Radius2563
  | 22 => fjmidP022Radius2563
  | 23 => fjmidP023Radius2563
  | 24 => fjmidP024Radius2563
  | 25 => fjmidP025Radius2563
  | 26 => fjmidP026Radius2563
  | 27 => fjmidP027Radius2563
  | 28 => fjmidP028Radius2563
  | 29 => fjmidP029Radius2563
  | _ => 0

theorem fjmidExpError2563 (i : Fin 30) :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 i edgeMidpointPosition2548 - fjmidValue2563 i‖
        ≤ fjmidError2563 i := by
  fin_cases i
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP000RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP001RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP002RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP003RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP004RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP005RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP006RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP007RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP008RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP009RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP010RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP011RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP012RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP013RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP014RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP015RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP016RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP017RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP018RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP019RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP020RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP021RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP022RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP023RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP024RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP025RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP026RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP027RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP028RoundedError2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP029RoundedError2563

theorem fjmidUnitNorm2563 (i : Fin 30) :
    ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤ 1 := by
  fin_cases i
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP000DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP001DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP002DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP003DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP004DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP005DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP006DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP007DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP008DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP009DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP010DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP011DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP012DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP013DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP014DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP015DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP016DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP017DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP018DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP019DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP020DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP021DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP022DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP023DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP024DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP025DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP026DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP027DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP028DerivativeNorm2563
  · simpa only [fjmidValue2563, fjmidError2563] using fjmidP029DerivativeNorm2563

noncomputable def fjmidSum2563 : ℂ := ⟨(((-(((105 * 10^40
        + 7804832256227226274689265144220988739093) * 10^40
        + 5695691877548110244416498304433764690364) * 10^40
        + 3698611850331482884623802678285990184017)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216)),
    (((((7 * 10^40
        + 8430992705165238783615494637993597117882) * 10^40
        + 3243323603153320536323948977512173292311) * 10^40
        + 3025436851772759049126449062497908213043) : ℝ) /
        (((5415370 * 10^40
        + 4963297165226140902034044603582742911628) * 10^40
        + 4339174837984293088793224180786254499995) * 10^40
        + 11922147613471467208908991351228465152))⟩

noncomputable def fjmidUpper2563 : ℝ := ((147 : ℝ) /
        50000000)

theorem fjmidSum_eq2563 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * fjmidValue2563 i) =
      fjmidSum2563 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, fjmidValue2563,
      fjmidSum2563, embedPair2542, fjmidP000Rounded2563,
      fjmidP001Rounded2563,
      fjmidP002Rounded2563,
      fjmidP003Rounded2563,
      fjmidP004Rounded2563,
      fjmidP005Rounded2563,
      fjmidP006Rounded2563,
      fjmidP007Rounded2563,
      fjmidP008Rounded2563,
      fjmidP009Rounded2563,
      fjmidP010Rounded2563,
      fjmidP011Rounded2563,
      fjmidP012Rounded2563,
      fjmidP013Rounded2563,
      fjmidP014Rounded2563,
      fjmidP015Rounded2563,
      fjmidP016Rounded2563,
      fjmidP017Rounded2563,
      fjmidP018Rounded2563,
      fjmidP019Rounded2563,
      fjmidP020Rounded2563,
      fjmidP021Rounded2563,
      fjmidP022Rounded2563,
      fjmidP023Rounded2563,
      fjmidP024Rounded2563,
      fjmidP025Rounded2563,
      fjmidP026Rounded2563,
      fjmidP027Rounded2563,
      fjmidP028Rounded2563,
      fjmidP029Rounded2563, Complex.mul_re, Complex.mul_im]

theorem fjmidSum_norm2563 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * fjmidValue2563 i‖ ≤ ((71 : ℝ) /
        25000000) := by
  rw [fjmidSum_eq2563]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [fjmidSum2563]

theorem fjmidCharge2563 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * fjmidError2563 i) ≤ (1 : ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, fjmidError2563,
      fjmidP000Radius2563,
      fjmidP001Radius2563,
      fjmidP002Radius2563,
      fjmidP003Radius2563,
      fjmidP004Radius2563,
      fjmidP005Radius2563,
      fjmidP006Radius2563,
      fjmidP007Radius2563,
      fjmidP008Radius2563,
      fjmidP009Radius2563,
      fjmidP010Radius2563,
      fjmidP011Radius2563,
      fjmidP012Radius2563,
      fjmidP013Radius2563,
      fjmidP014Radius2563,
      fjmidP015Radius2563,
      fjmidP016Radius2563,
      fjmidP017Radius2563,
      fjmidP018Radius2563,
      fjmidP019Radius2563,
      fjmidP020Radius2563,
      fjmidP021Radius2563,
      fjmidP022Radius2563,
      fjmidP023Radius2563,
      fjmidP024Radius2563,
      fjmidP025Radius2563,
      fjmidP026Radius2563,
      fjmidP027Radius2563,
      fjmidP028Radius2563,
      fjmidP029Radius2563]

theorem firstJetMidpointUpper_le2563 :
    signedJetUpper2539 1 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 edgeMidpointPosition2548 ≤ fjmidUpper2563 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 1 (1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * fjmidValue2563 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * fjmidError2563 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (fjmidExpError2563 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (fjmidUnitNorm2563 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 1 (1/2) nodeModulation2541 i edgeMidpointPosition2548‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 fjmidUpper2563
  linarith [fjmidSum_norm2563, fjmidCharge2563]

theorem weightedPhysicalFirstJetMidpoint_le2563 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 1 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        edgeMidpointPosition2548‖ ≤
      fjmidUpper2563 := by
  have h := weightedPhysical2539_jet_le_center_error 1 (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        edgeMidpointPosition2548
  exact h.trans firstJetMidpointUpper_le2563

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.fjmidExpError2563
#print axioms ConnesWeilRH.Dev.fjmidSum_eq2563
#print axioms ConnesWeilRH.Dev.fjmidSum_norm2563
#print axioms ConnesWeilRH.Dev.fjmidCharge2563
#print axioms ConnesWeilRH.Dev.firstJetMidpointUpper_le2563
#print axioms ConnesWeilRH.Dev.weightedPhysicalFirstJetMidpoint_le2563
