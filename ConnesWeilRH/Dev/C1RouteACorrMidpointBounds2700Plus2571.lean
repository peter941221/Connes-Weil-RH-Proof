import ConnesWeilRH.Dev.C1RouteACorrPlusMidpointDerivatives2571
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem corrC02700PlusMidpoint_triangle2571 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def corrC02700PlusMidpointP000Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP000Radius2571 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrC02700PlusMidpointP000RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP000Factor2571
        corrC02700PlusMidpointP000Center2571) =
        corrC02700PlusMidpointP000Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP000RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP000Rounded2571‖ ≤ corrC02700PlusMidpointP000Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP000Factor2571
      corrC02700PlusMidpointP000Center2571)
  rw [corrC02700PlusMidpointP000RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP000Factor2571 * embedPair2542
        corrC02700PlusMidpointP000Center2571)
    (embedPair2542 corrC02700PlusMidpointP000Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP000DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP000Factor2571,
      corrC02700PlusMidpointP000Error2571, rounding2542,
      corrC02700PlusMidpointP000Radius2571]

theorem corrC02700PlusMidpointP000DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP000Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP000RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP000Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP000Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP000Rounded2571]

def corrC02700PlusMidpointP001Rounded2571 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP001Radius2571 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700PlusMidpointP001RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP001Factor2571
        corrC02700PlusMidpointP001Center2571) =
        corrC02700PlusMidpointP001Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP001RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP001Rounded2571‖ ≤ corrC02700PlusMidpointP001Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP001Factor2571
      corrC02700PlusMidpointP001Center2571)
  rw [corrC02700PlusMidpointP001RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP001Factor2571 * embedPair2542
        corrC02700PlusMidpointP001Center2571)
    (embedPair2542 corrC02700PlusMidpointP001Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP001DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP001Factor2571,
      corrC02700PlusMidpointP001Error2571, rounding2542,
      corrC02700PlusMidpointP001Radius2571]

theorem corrC02700PlusMidpointP001DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP001Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP001RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP001Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP001Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP001Rounded2571]

def corrC02700PlusMidpointP002Rounded2571 : RatPair2542 :=
  (((1339907 : ℚ) /
        1267650600228229401496703205376),
    (((-524869) : ℚ) /
        633825300114114700748351602688))

noncomputable def corrC02700PlusMidpointP002Radius2571 : ℝ := ((2199023262191 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700PlusMidpointP002RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP002Factor2571
        corrC02700PlusMidpointP002Center2571) =
        corrC02700PlusMidpointP002Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP002RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP002Rounded2571‖ ≤ corrC02700PlusMidpointP002Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP002Factor2571
      corrC02700PlusMidpointP002Center2571)
  rw [corrC02700PlusMidpointP002RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP002Factor2571 * embedPair2542
        corrC02700PlusMidpointP002Center2571)
    (embedPair2542 corrC02700PlusMidpointP002Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP002DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP002Factor2571,
      corrC02700PlusMidpointP002Error2571, rounding2542,
      corrC02700PlusMidpointP002Radius2571]

theorem corrC02700PlusMidpointP002DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP002Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP002RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP002Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP002Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP002Rounded2571]

def corrC02700PlusMidpointP003Rounded2571 : RatPair2542 :=
  (((15448181489715 : ℚ) /
        1267650600228229401496703205376),
    ((3802480427995 : ℚ) /
        1267650600228229401496703205376))

noncomputable def corrC02700PlusMidpointP003Radius2571 : ℝ := ((569261515263 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrC02700PlusMidpointP003RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP003Factor2571
        corrC02700PlusMidpointP003Center2571) =
        corrC02700PlusMidpointP003Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP003RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP003Rounded2571‖ ≤ corrC02700PlusMidpointP003Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP003Factor2571
      corrC02700PlusMidpointP003Center2571)
  rw [corrC02700PlusMidpointP003RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP003Factor2571 * embedPair2542
        corrC02700PlusMidpointP003Center2571)
    (embedPair2542 corrC02700PlusMidpointP003Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP003DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP003Factor2571,
      corrC02700PlusMidpointP003Error2571, rounding2542,
      corrC02700PlusMidpointP003Radius2571]

theorem corrC02700PlusMidpointP003DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP003Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP003RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP003Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP003Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP003Rounded2571]

def corrC02700PlusMidpointP004Rounded2571 : RatPair2542 :=
  (((762028936138355 : ℚ) /
        158456325028528675187087900672),
    (((-1970922237903599) : ℚ) /
        633825300114114700748351602688))

noncomputable def corrC02700PlusMidpointP004Radius2571 : ℝ := ((17135354181433 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02700PlusMidpointP004RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP004Factor2571
        corrC02700PlusMidpointP004Center2571) =
        corrC02700PlusMidpointP004Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP004RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP004Rounded2571‖ ≤ corrC02700PlusMidpointP004Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP004Factor2571
      corrC02700PlusMidpointP004Center2571)
  rw [corrC02700PlusMidpointP004RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP004Factor2571 * embedPair2542
        corrC02700PlusMidpointP004Center2571)
    (embedPair2542 corrC02700PlusMidpointP004Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP004DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP004Factor2571,
      corrC02700PlusMidpointP004Error2571, rounding2542,
      corrC02700PlusMidpointP004Radius2571]

theorem corrC02700PlusMidpointP004DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP004Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP004RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP004Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP004Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP004Rounded2571]

def corrC02700PlusMidpointP005Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP005Radius2571 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrC02700PlusMidpointP005RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP005Factor2571
        corrC02700PlusMidpointP005Center2571) =
        corrC02700PlusMidpointP005Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP005RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP005Rounded2571‖ ≤ corrC02700PlusMidpointP005Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP005Factor2571
      corrC02700PlusMidpointP005Center2571)
  rw [corrC02700PlusMidpointP005RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP005Factor2571 * embedPair2542
        corrC02700PlusMidpointP005Center2571)
    (embedPair2542 corrC02700PlusMidpointP005Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP005DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP005Factor2571,
      corrC02700PlusMidpointP005Error2571, rounding2542,
      corrC02700PlusMidpointP005Radius2571]

theorem corrC02700PlusMidpointP005DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP005Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP005RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP005Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP005Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP005Rounded2571]

def corrC02700PlusMidpointP006Rounded2571 : RatPair2542 :=
  (((1 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP006Radius2571 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700PlusMidpointP006RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP006Factor2571
        corrC02700PlusMidpointP006Center2571) =
        corrC02700PlusMidpointP006Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP006RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP006Rounded2571‖ ≤ corrC02700PlusMidpointP006Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP006Factor2571
      corrC02700PlusMidpointP006Center2571)
  rw [corrC02700PlusMidpointP006RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP006Factor2571 * embedPair2542
        corrC02700PlusMidpointP006Center2571)
    (embedPair2542 corrC02700PlusMidpointP006Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP006DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP006Factor2571,
      corrC02700PlusMidpointP006Error2571, rounding2542,
      corrC02700PlusMidpointP006Radius2571]

theorem corrC02700PlusMidpointP006DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP006Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP006RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP006Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP006Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP006Rounded2571]

def corrC02700PlusMidpointP007Rounded2571 : RatPair2542 :=
  (((1852709455279 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP007Radius2571 : ℝ := ((1099646212197 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02700PlusMidpointP007RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP007Factor2571
        corrC02700PlusMidpointP007Center2571) =
        corrC02700PlusMidpointP007Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP007RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP007Rounded2571‖ ≤ corrC02700PlusMidpointP007Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP007Factor2571
      corrC02700PlusMidpointP007Center2571)
  rw [corrC02700PlusMidpointP007RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP007Factor2571 * embedPair2542
        corrC02700PlusMidpointP007Center2571)
    (embedPair2542 corrC02700PlusMidpointP007Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP007DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP007Factor2571,
      corrC02700PlusMidpointP007Error2571, rounding2542,
      corrC02700PlusMidpointP007Radius2571]

theorem corrC02700PlusMidpointP007DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP007Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP007RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP007Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP007Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP007Rounded2571]

def corrC02700PlusMidpointP008Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP008Radius2571 : ℝ := ((2223573724293 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700PlusMidpointP008RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP008Factor2571
        corrC02700PlusMidpointP008Center2571) =
        corrC02700PlusMidpointP008Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP008RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP008Rounded2571‖ ≤ corrC02700PlusMidpointP008Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP008Factor2571
      corrC02700PlusMidpointP008Center2571)
  rw [corrC02700PlusMidpointP008RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP008Factor2571 * embedPair2542
        corrC02700PlusMidpointP008Center2571)
    (embedPair2542 corrC02700PlusMidpointP008Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP008DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP008Factor2571,
      corrC02700PlusMidpointP008Error2571, rounding2542,
      corrC02700PlusMidpointP008Radius2571]

theorem corrC02700PlusMidpointP008DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP008Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP008RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP008Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP008Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP008Rounded2571]

def corrC02700PlusMidpointP009Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP009Radius2571 : ℝ := ((1111786863637 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02700PlusMidpointP009RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP009Factor2571
        corrC02700PlusMidpointP009Center2571) =
        corrC02700PlusMidpointP009Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP009RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP009Rounded2571‖ ≤ corrC02700PlusMidpointP009Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP009Factor2571
      corrC02700PlusMidpointP009Center2571)
  rw [corrC02700PlusMidpointP009RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP009Factor2571 * embedPair2542
        corrC02700PlusMidpointP009Center2571)
    (embedPair2542 corrC02700PlusMidpointP009Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP009DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP009Factor2571,
      corrC02700PlusMidpointP009Error2571, rounding2542,
      corrC02700PlusMidpointP009Radius2571]

theorem corrC02700PlusMidpointP009DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP009Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP009RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP009Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP009Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP009Rounded2571]

def corrC02700PlusMidpointP010Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP010Radius2571 : ℝ := ((2223573729001 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700PlusMidpointP010RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP010Factor2571
        corrC02700PlusMidpointP010Center2571) =
        corrC02700PlusMidpointP010Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP010RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP010Rounded2571‖ ≤ corrC02700PlusMidpointP010Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP010Factor2571
      corrC02700PlusMidpointP010Center2571)
  rw [corrC02700PlusMidpointP010RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP010Factor2571 * embedPair2542
        corrC02700PlusMidpointP010Center2571)
    (embedPair2542 corrC02700PlusMidpointP010Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP010DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP010Factor2571,
      corrC02700PlusMidpointP010Error2571, rounding2542,
      corrC02700PlusMidpointP010Radius2571]

theorem corrC02700PlusMidpointP010DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP010Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP010RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP010Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP010Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP010Rounded2571]

def corrC02700PlusMidpointP011Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP011Radius2571 : ℝ := ((277946716269 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem corrC02700PlusMidpointP011RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP011Factor2571
        corrC02700PlusMidpointP011Center2571) =
        corrC02700PlusMidpointP011Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP011RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP011Rounded2571‖ ≤ corrC02700PlusMidpointP011Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP011Factor2571
      corrC02700PlusMidpointP011Center2571)
  rw [corrC02700PlusMidpointP011RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP011Factor2571 * embedPair2542
        corrC02700PlusMidpointP011Center2571)
    (embedPair2542 corrC02700PlusMidpointP011Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP011DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP011Factor2571,
      corrC02700PlusMidpointP011Error2571, rounding2542,
      corrC02700PlusMidpointP011Radius2571]

theorem corrC02700PlusMidpointP011DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP011Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP011RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP011Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP011Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP011Rounded2571]

def corrC02700PlusMidpointP012Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP012Radius2571 : ℝ := ((138973358209 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem corrC02700PlusMidpointP012RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP012Factor2571
        corrC02700PlusMidpointP012Center2571) =
        corrC02700PlusMidpointP012Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP012RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP012Rounded2571‖ ≤ corrC02700PlusMidpointP012Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP012Factor2571
      corrC02700PlusMidpointP012Center2571)
  rw [corrC02700PlusMidpointP012RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP012Factor2571 * embedPair2542
        corrC02700PlusMidpointP012Center2571)
    (embedPair2542 corrC02700PlusMidpointP012Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP012DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP012Factor2571,
      corrC02700PlusMidpointP012Error2571, rounding2542,
      corrC02700PlusMidpointP012Radius2571]

theorem corrC02700PlusMidpointP012DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP012Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP012RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP012Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP012Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP012Rounded2571]

def corrC02700PlusMidpointP013Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP013Radius2571 : ℝ := ((1111786866215 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02700PlusMidpointP013RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP013Factor2571
        corrC02700PlusMidpointP013Center2571) =
        corrC02700PlusMidpointP013Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP013RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP013Rounded2571‖ ≤ corrC02700PlusMidpointP013Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP013Factor2571
      corrC02700PlusMidpointP013Center2571)
  rw [corrC02700PlusMidpointP013RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP013Factor2571 * embedPair2542
        corrC02700PlusMidpointP013Center2571)
    (embedPair2542 corrC02700PlusMidpointP013Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP013DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP013Factor2571,
      corrC02700PlusMidpointP013Error2571, rounding2542,
      corrC02700PlusMidpointP013Radius2571]

theorem corrC02700PlusMidpointP013DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP013Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP013RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP013Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP013Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP013Rounded2571]

def corrC02700PlusMidpointP014Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP014Radius2571 : ℝ := ((2223573734443 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700PlusMidpointP014RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP014Factor2571
        corrC02700PlusMidpointP014Center2571) =
        corrC02700PlusMidpointP014Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP014RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP014Rounded2571‖ ≤ corrC02700PlusMidpointP014Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP014Factor2571
      corrC02700PlusMidpointP014Center2571)
  rw [corrC02700PlusMidpointP014RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP014Factor2571 * embedPair2542
        corrC02700PlusMidpointP014Center2571)
    (embedPair2542 corrC02700PlusMidpointP014Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP014DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP014Factor2571,
      corrC02700PlusMidpointP014Error2571, rounding2542,
      corrC02700PlusMidpointP014Radius2571]

theorem corrC02700PlusMidpointP014DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP014Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP014RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP014Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP014Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP014Rounded2571]

def corrC02700PlusMidpointP015Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP015Radius2571 : ℝ := ((2223573735885 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700PlusMidpointP015RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP015Factor2571
        corrC02700PlusMidpointP015Center2571) =
        corrC02700PlusMidpointP015Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP015RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP015Rounded2571‖ ≤ corrC02700PlusMidpointP015Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP015Factor2571
      corrC02700PlusMidpointP015Center2571)
  rw [corrC02700PlusMidpointP015RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP015Factor2571 * embedPair2542
        corrC02700PlusMidpointP015Center2571)
    (embedPair2542 corrC02700PlusMidpointP015Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP015DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP015Factor2571,
      corrC02700PlusMidpointP015Error2571, rounding2542,
      corrC02700PlusMidpointP015Radius2571]

theorem corrC02700PlusMidpointP015DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP015Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP015RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP015Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP015Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP015Rounded2571]

def corrC02700PlusMidpointP016Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP016Radius2571 : ℝ := ((69486679279 : ℝ) /
        (4 * 10^40
        + 3556142965880123323311949751266331066368))

theorem corrC02700PlusMidpointP016RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP016Factor2571
        corrC02700PlusMidpointP016Center2571) =
        corrC02700PlusMidpointP016Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP016RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP016Rounded2571‖ ≤ corrC02700PlusMidpointP016Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP016Factor2571
      corrC02700PlusMidpointP016Center2571)
  rw [corrC02700PlusMidpointP016RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP016Factor2571 * embedPair2542
        corrC02700PlusMidpointP016Center2571)
    (embedPair2542 corrC02700PlusMidpointP016Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP016DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP016Factor2571,
      corrC02700PlusMidpointP016Error2571, rounding2542,
      corrC02700PlusMidpointP016Radius2571]

theorem corrC02700PlusMidpointP016DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP016Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP016RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP016Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP016Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP016Rounded2571]

def corrC02700PlusMidpointP017Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP017Radius2571 : ℝ := ((277946717369 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem corrC02700PlusMidpointP017RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP017Factor2571
        corrC02700PlusMidpointP017Center2571) =
        corrC02700PlusMidpointP017Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP017RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP017Rounded2571‖ ≤ corrC02700PlusMidpointP017Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP017Factor2571
      corrC02700PlusMidpointP017Center2571)
  rw [corrC02700PlusMidpointP017RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP017Factor2571 * embedPair2542
        corrC02700PlusMidpointP017Center2571)
    (embedPair2542 corrC02700PlusMidpointP017Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP017DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP017Factor2571,
      corrC02700PlusMidpointP017Error2571, rounding2542,
      corrC02700PlusMidpointP017Radius2571]

theorem corrC02700PlusMidpointP017DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP017Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP017RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP017Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP017Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP017Rounded2571]

def corrC02700PlusMidpointP018Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP018Radius2571 : ℝ := ((1111786869859 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02700PlusMidpointP018RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP018Factor2571
        corrC02700PlusMidpointP018Center2571) =
        corrC02700PlusMidpointP018Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP018RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP018Rounded2571‖ ≤ corrC02700PlusMidpointP018Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP018Factor2571
      corrC02700PlusMidpointP018Center2571)
  rw [corrC02700PlusMidpointP018RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP018Factor2571 * embedPair2542
        corrC02700PlusMidpointP018Center2571)
    (embedPair2542 corrC02700PlusMidpointP018Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP018DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP018Factor2571,
      corrC02700PlusMidpointP018Error2571, rounding2542,
      corrC02700PlusMidpointP018Radius2571]

theorem corrC02700PlusMidpointP018DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP018Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP018RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP018Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP018Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP018Rounded2571]

def corrC02700PlusMidpointP019Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP019Radius2571 : ℝ := ((2223573741101 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700PlusMidpointP019RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP019Factor2571
        corrC02700PlusMidpointP019Center2571) =
        corrC02700PlusMidpointP019Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP019RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP019Rounded2571‖ ≤ corrC02700PlusMidpointP019Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP019Factor2571
      corrC02700PlusMidpointP019Center2571)
  rw [corrC02700PlusMidpointP019RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP019Factor2571 * embedPair2542
        corrC02700PlusMidpointP019Center2571)
    (embedPair2542 corrC02700PlusMidpointP019Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP019DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP019Factor2571,
      corrC02700PlusMidpointP019Error2571, rounding2542,
      corrC02700PlusMidpointP019Radius2571]

theorem corrC02700PlusMidpointP019DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP019Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP019RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP019Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP019Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP019Rounded2571]

def corrC02700PlusMidpointP020Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP020Radius2571 : ℝ := ((1111786871303 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02700PlusMidpointP020RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP020Factor2571
        corrC02700PlusMidpointP020Center2571) =
        corrC02700PlusMidpointP020Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP020RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP020Rounded2571‖ ≤ corrC02700PlusMidpointP020Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP020Factor2571
      corrC02700PlusMidpointP020Center2571)
  rw [corrC02700PlusMidpointP020RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP020Factor2571 * embedPair2542
        corrC02700PlusMidpointP020Center2571)
    (embedPair2542 corrC02700PlusMidpointP020Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP020DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP020Factor2571,
      corrC02700PlusMidpointP020Error2571, rounding2542,
      corrC02700PlusMidpointP020Radius2571]

theorem corrC02700PlusMidpointP020DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP020Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP020RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP020Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP020Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP020Rounded2571]

def corrC02700PlusMidpointP021Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP021Radius2571 : ℝ := ((2223573743861 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700PlusMidpointP021RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP021Factor2571
        corrC02700PlusMidpointP021Center2571) =
        corrC02700PlusMidpointP021Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP021RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP021Rounded2571‖ ≤ corrC02700PlusMidpointP021Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP021Factor2571
      corrC02700PlusMidpointP021Center2571)
  rw [corrC02700PlusMidpointP021RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP021Factor2571 * embedPair2542
        corrC02700PlusMidpointP021Center2571)
    (embedPair2542 corrC02700PlusMidpointP021Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP021DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP021Factor2571,
      corrC02700PlusMidpointP021Error2571, rounding2542,
      corrC02700PlusMidpointP021Radius2571]

theorem corrC02700PlusMidpointP021DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP021Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP021RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP021Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP021Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP021Rounded2571]

def corrC02700PlusMidpointP022Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP022Radius2571 : ℝ := ((277946718063 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem corrC02700PlusMidpointP022RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP022Factor2571
        corrC02700PlusMidpointP022Center2571) =
        corrC02700PlusMidpointP022Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP022RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP022Rounded2571‖ ≤ corrC02700PlusMidpointP022Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP022Factor2571
      corrC02700PlusMidpointP022Center2571)
  rw [corrC02700PlusMidpointP022RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP022Factor2571 * embedPair2542
        corrC02700PlusMidpointP022Center2571)
    (embedPair2542 corrC02700PlusMidpointP022Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP022DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP022Factor2571,
      corrC02700PlusMidpointP022Error2571, rounding2542,
      corrC02700PlusMidpointP022Radius2571]

theorem corrC02700PlusMidpointP022DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP022Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP022RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP022Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP022Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP022Rounded2571]

def corrC02700PlusMidpointP023Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP023Radius2571 : ℝ := ((555893436589 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrC02700PlusMidpointP023RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP023Factor2571
        corrC02700PlusMidpointP023Center2571) =
        corrC02700PlusMidpointP023Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP023RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP023Rounded2571‖ ≤ corrC02700PlusMidpointP023Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP023Factor2571
      corrC02700PlusMidpointP023Center2571)
  rw [corrC02700PlusMidpointP023RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP023Factor2571 * embedPair2542
        corrC02700PlusMidpointP023Center2571)
    (embedPair2542 corrC02700PlusMidpointP023Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP023DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP023Factor2571,
      corrC02700PlusMidpointP023Error2571, rounding2542,
      corrC02700PlusMidpointP023Radius2571]

theorem corrC02700PlusMidpointP023DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP023Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP023RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP023Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP023Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP023Rounded2571]

def corrC02700PlusMidpointP024Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP024Radius2571 : ℝ := ((277946718401 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem corrC02700PlusMidpointP024RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP024Factor2571
        corrC02700PlusMidpointP024Center2571) =
        corrC02700PlusMidpointP024Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP024RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP024Rounded2571‖ ≤ corrC02700PlusMidpointP024Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP024Factor2571
      corrC02700PlusMidpointP024Center2571)
  rw [corrC02700PlusMidpointP024RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP024Factor2571 * embedPair2542
        corrC02700PlusMidpointP024Center2571)
    (embedPair2542 corrC02700PlusMidpointP024Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP024DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP024Factor2571,
      corrC02700PlusMidpointP024Error2571, rounding2542,
      corrC02700PlusMidpointP024Radius2571]

theorem corrC02700PlusMidpointP024DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP024Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP024RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP024Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP024Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP024Rounded2571]

def corrC02700PlusMidpointP025Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP025Radius2571 : ℝ := ((2223573748275 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700PlusMidpointP025RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP025Factor2571
        corrC02700PlusMidpointP025Center2571) =
        corrC02700PlusMidpointP025Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP025RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP025Rounded2571‖ ≤ corrC02700PlusMidpointP025Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP025Factor2571
      corrC02700PlusMidpointP025Center2571)
  rw [corrC02700PlusMidpointP025RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP025Factor2571 * embedPair2542
        corrC02700PlusMidpointP025Center2571)
    (embedPair2542 corrC02700PlusMidpointP025Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP025DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP025Factor2571,
      corrC02700PlusMidpointP025Error2571, rounding2542,
      corrC02700PlusMidpointP025Radius2571]

theorem corrC02700PlusMidpointP025DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP025Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP025RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP025Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP025Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP025Rounded2571]

def corrC02700PlusMidpointP026Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP026Radius2571 : ℝ := ((1111786874683 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02700PlusMidpointP026RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP026Factor2571
        corrC02700PlusMidpointP026Center2571) =
        corrC02700PlusMidpointP026Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP026RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP026Rounded2571‖ ≤ corrC02700PlusMidpointP026Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP026Factor2571
      corrC02700PlusMidpointP026Center2571)
  rw [corrC02700PlusMidpointP026RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP026Factor2571 * embedPair2542
        corrC02700PlusMidpointP026Center2571)
    (embedPair2542 corrC02700PlusMidpointP026Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP026DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP026Factor2571,
      corrC02700PlusMidpointP026Error2571, rounding2542,
      corrC02700PlusMidpointP026Radius2571]

theorem corrC02700PlusMidpointP026DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP026Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP026RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP026Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP026Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP026Rounded2571]

def corrC02700PlusMidpointP027Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP027Radius2571 : ℝ := ((555893437735 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrC02700PlusMidpointP027RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP027Factor2571
        corrC02700PlusMidpointP027Center2571) =
        corrC02700PlusMidpointP027Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP027RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP027Rounded2571‖ ≤ corrC02700PlusMidpointP027Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP027Factor2571
      corrC02700PlusMidpointP027Center2571)
  rw [corrC02700PlusMidpointP027RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP027Factor2571 * embedPair2542
        corrC02700PlusMidpointP027Center2571)
    (embedPair2542 corrC02700PlusMidpointP027Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP027DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP027Factor2571,
      corrC02700PlusMidpointP027Error2571, rounding2542,
      corrC02700PlusMidpointP027Radius2571]

theorem corrC02700PlusMidpointP027DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP027Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP027RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP027Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP027Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP027Rounded2571]

def corrC02700PlusMidpointP028Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP028Radius2571 : ℝ := ((555893437891 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrC02700PlusMidpointP028RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP028Factor2571
        corrC02700PlusMidpointP028Center2571) =
        corrC02700PlusMidpointP028Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP028RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP028Rounded2571‖ ≤ corrC02700PlusMidpointP028Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP028Factor2571
      corrC02700PlusMidpointP028Center2571)
  rw [corrC02700PlusMidpointP028RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP028Factor2571 * embedPair2542
        corrC02700PlusMidpointP028Center2571)
    (embedPair2542 corrC02700PlusMidpointP028Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP028DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP028Factor2571,
      corrC02700PlusMidpointP028Error2571, rounding2542,
      corrC02700PlusMidpointP028Radius2571]

theorem corrC02700PlusMidpointP028DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP028Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP028RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP028Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP028Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP028Rounded2571]

def corrC02700PlusMidpointP029Rounded2571 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700PlusMidpointP029Radius2571 : ℝ := ((2223573752513 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700PlusMidpointP029RoundCompute2571 :
    pairRound2542 (pairMul2542 corrC02700PlusMidpointP029Factor2571
        corrC02700PlusMidpointP029Center2571) =
        corrC02700PlusMidpointP029Rounded2571 := by
  cbv

theorem corrC02700PlusMidpointP029RoundedError2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02700PlusMidpointPosition2571 -
      embedPair2542 corrC02700PlusMidpointP029Rounded2571‖ ≤ corrC02700PlusMidpointP029Radius2571
          := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700PlusMidpointP029Factor2571
      corrC02700PlusMidpointP029Center2571)
  rw [corrC02700PlusMidpointP029RoundCompute2571, embedPair_mul2542] at hr
  have h := (corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP029Factor2571 * embedPair2542
        corrC02700PlusMidpointP029Center2571)
    (embedPair2542 corrC02700PlusMidpointP029Rounded2571)).trans (add_le_add
        corrC02700PlusMidpointP029DerivativeError2571 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700PlusMidpointP029Factor2571,
      corrC02700PlusMidpointP029Error2571, rounding2542,
      corrC02700PlusMidpointP029Radius2571]

theorem corrC02700PlusMidpointP029DerivativeNorm2571 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02700PlusMidpointPosition2571‖ ≤ 1 := by
  have h := corrC02700PlusMidpoint_triangle2571
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02700PlusMidpointPosition2571)
    (embedPair2542 corrC02700PlusMidpointP029Rounded2571) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700PlusMidpointP029RoundedError2571
      (embedPair_magnitude2542
      corrC02700PlusMidpointP029Rounded2571))
  apply h'.trans
  norm_num [corrC02700PlusMidpointP029Radius2571, pairMagnitude2542,
      corrC02700PlusMidpointP029Rounded2571]

noncomputable def corrC02700PlusSignedMidpointValue2571 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 corrC02700PlusMidpointP000Rounded2571
  | 1 => embedPair2542 corrC02700PlusMidpointP001Rounded2571
  | 2 => embedPair2542 corrC02700PlusMidpointP002Rounded2571
  | 3 => embedPair2542 corrC02700PlusMidpointP003Rounded2571
  | 4 => embedPair2542 corrC02700PlusMidpointP004Rounded2571
  | 5 => embedPair2542 corrC02700PlusMidpointP005Rounded2571
  | 6 => embedPair2542 corrC02700PlusMidpointP006Rounded2571
  | 7 => embedPair2542 corrC02700PlusMidpointP007Rounded2571
  | 8 => embedPair2542 corrC02700PlusMidpointP008Rounded2571
  | 9 => embedPair2542 corrC02700PlusMidpointP009Rounded2571
  | 10 => embedPair2542 corrC02700PlusMidpointP010Rounded2571
  | 11 => embedPair2542 corrC02700PlusMidpointP011Rounded2571
  | 12 => embedPair2542 corrC02700PlusMidpointP012Rounded2571
  | 13 => embedPair2542 corrC02700PlusMidpointP013Rounded2571
  | 14 => embedPair2542 corrC02700PlusMidpointP014Rounded2571
  | 15 => embedPair2542 corrC02700PlusMidpointP015Rounded2571
  | 16 => embedPair2542 corrC02700PlusMidpointP016Rounded2571
  | 17 => embedPair2542 corrC02700PlusMidpointP017Rounded2571
  | 18 => embedPair2542 corrC02700PlusMidpointP018Rounded2571
  | 19 => embedPair2542 corrC02700PlusMidpointP019Rounded2571
  | 20 => embedPair2542 corrC02700PlusMidpointP020Rounded2571
  | 21 => embedPair2542 corrC02700PlusMidpointP021Rounded2571
  | 22 => embedPair2542 corrC02700PlusMidpointP022Rounded2571
  | 23 => embedPair2542 corrC02700PlusMidpointP023Rounded2571
  | 24 => embedPair2542 corrC02700PlusMidpointP024Rounded2571
  | 25 => embedPair2542 corrC02700PlusMidpointP025Rounded2571
  | 26 => embedPair2542 corrC02700PlusMidpointP026Rounded2571
  | 27 => embedPair2542 corrC02700PlusMidpointP027Rounded2571
  | 28 => embedPair2542 corrC02700PlusMidpointP028Rounded2571
  | 29 => embedPair2542 corrC02700PlusMidpointP029Rounded2571
  | _ => 0

noncomputable def corrC02700PlusSignedMidpointError2571 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => corrC02700PlusMidpointP000Radius2571
  | 1 => corrC02700PlusMidpointP001Radius2571
  | 2 => corrC02700PlusMidpointP002Radius2571
  | 3 => corrC02700PlusMidpointP003Radius2571
  | 4 => corrC02700PlusMidpointP004Radius2571
  | 5 => corrC02700PlusMidpointP005Radius2571
  | 6 => corrC02700PlusMidpointP006Radius2571
  | 7 => corrC02700PlusMidpointP007Radius2571
  | 8 => corrC02700PlusMidpointP008Radius2571
  | 9 => corrC02700PlusMidpointP009Radius2571
  | 10 => corrC02700PlusMidpointP010Radius2571
  | 11 => corrC02700PlusMidpointP011Radius2571
  | 12 => corrC02700PlusMidpointP012Radius2571
  | 13 => corrC02700PlusMidpointP013Radius2571
  | 14 => corrC02700PlusMidpointP014Radius2571
  | 15 => corrC02700PlusMidpointP015Radius2571
  | 16 => corrC02700PlusMidpointP016Radius2571
  | 17 => corrC02700PlusMidpointP017Radius2571
  | 18 => corrC02700PlusMidpointP018Radius2571
  | 19 => corrC02700PlusMidpointP019Radius2571
  | 20 => corrC02700PlusMidpointP020Radius2571
  | 21 => corrC02700PlusMidpointP021Radius2571
  | 22 => corrC02700PlusMidpointP022Radius2571
  | 23 => corrC02700PlusMidpointP023Radius2571
  | 24 => corrC02700PlusMidpointP024Radius2571
  | 25 => corrC02700PlusMidpointP025Radius2571
  | 26 => corrC02700PlusMidpointP026Radius2571
  | 27 => corrC02700PlusMidpointP027Radius2571
  | 28 => corrC02700PlusMidpointP028Radius2571
  | 29 => corrC02700PlusMidpointP029Radius2571
  | _ => 0

theorem corrC02700PlusSignedMidpointExpError2571 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrC02700PlusMidpointPosition2571 -
        corrC02700PlusSignedMidpointValue2571 i‖ ≤ corrC02700PlusSignedMidpointError2571 i := by
  fin_cases i
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP000RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP001RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP002RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP003RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP004RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP005RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP006RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP007RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP008RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP009RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP010RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP011RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP012RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP013RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP014RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP015RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP016RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP017RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP018RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP019RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP020RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP021RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP022RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP023RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP024RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP025RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP026RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP027RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP028RoundedError2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP029RoundedError2571

theorem corrC02700PlusSignedMidpointUnitNorm2571 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrC02700PlusMidpointPosition2571‖ ≤ 1 :=
        by
  fin_cases i
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP000DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP001DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP002DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP003DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP004DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP005DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP006DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP007DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP008DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP009DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP010DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP011DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP012DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP013DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP014DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP015DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP016DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP017DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP018DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP019DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP020DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP021DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP022DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP023DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP024DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP025DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP026DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP027DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP028DerivativeNorm2571
  · simpa only [corrC02700PlusSignedMidpointValue2571, corrC02700PlusSignedMidpointError2571]
      using
      corrC02700PlusMidpointP029DerivativeNorm2571

noncomputable def corrC02700PlusSignedMidpointSum2571 : ℂ := ⟨(((-(((1512861597016 * 10^40
        + 5736811035778026656153398774944207031669) * 10^40
        + 2897914615118853429968244721765009410485) * 10^40
        + 8643098630596266898736334414851504512237)) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888)),
    (((((234235013258 * 10^40
        + 2571168900627108568338110160184839747444) * 10^40
        + 4982942623577105665006200311060987478326) * 10^40
        + 1314365141740848877379992013577891199497) : ℝ) /
        (((709803441694 * 10^40
        + 9286040520740311406294280797278912962090) * 10^40
        + 4324364277263734305479824015949823344796) * 10^40
        + 2659731992932150006119314388217384402944))⟩

noncomputable def corrC02700PlusSignedMidpointUpper2571 : ℝ := ((111561481 : ℝ) /
        100000000)

theorem corrC02700PlusSignedMidpointSum_eq2571 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * corrC02700PlusSignedMidpointValue2571 i) =
      corrC02700PlusSignedMidpointSum2571 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        corrC02700PlusSignedMidpointValue2571,
      corrC02700PlusSignedMidpointSum2571, embedPair2542, corrC02700PlusMidpointP000Rounded2571,
      corrC02700PlusMidpointP001Rounded2571,
      corrC02700PlusMidpointP002Rounded2571,
      corrC02700PlusMidpointP003Rounded2571,
      corrC02700PlusMidpointP004Rounded2571,
      corrC02700PlusMidpointP005Rounded2571,
      corrC02700PlusMidpointP006Rounded2571,
      corrC02700PlusMidpointP007Rounded2571,
      corrC02700PlusMidpointP008Rounded2571,
      corrC02700PlusMidpointP009Rounded2571,
      corrC02700PlusMidpointP010Rounded2571,
      corrC02700PlusMidpointP011Rounded2571,
      corrC02700PlusMidpointP012Rounded2571,
      corrC02700PlusMidpointP013Rounded2571,
      corrC02700PlusMidpointP014Rounded2571,
      corrC02700PlusMidpointP015Rounded2571,
      corrC02700PlusMidpointP016Rounded2571,
      corrC02700PlusMidpointP017Rounded2571,
      corrC02700PlusMidpointP018Rounded2571,
      corrC02700PlusMidpointP019Rounded2571,
      corrC02700PlusMidpointP020Rounded2571,
      corrC02700PlusMidpointP021Rounded2571,
      corrC02700PlusMidpointP022Rounded2571,
      corrC02700PlusMidpointP023Rounded2571,
      corrC02700PlusMidpointP024Rounded2571,
      corrC02700PlusMidpointP025Rounded2571,
      corrC02700PlusMidpointP026Rounded2571,
      corrC02700PlusMidpointP027Rounded2571,
      corrC02700PlusMidpointP028Rounded2571,
      corrC02700PlusMidpointP029Rounded2571, Complex.mul_re, Complex.mul_im]

theorem corrC02700PlusSignedMidpointSum_norm2571 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrC02700PlusSignedMidpointValue2571 i‖ ≤
        ((111561471 :
        ℝ) /
        100000000) := by
  rw [corrC02700PlusSignedMidpointSum_eq2571]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [corrC02700PlusSignedMidpointSum2571]

theorem corrC02700PlusSignedMidpointCharge2571 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * corrC02700PlusSignedMidpointError2571 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      corrC02700PlusSignedMidpointError2571, corrC02700PlusMidpointP000Radius2571,
      corrC02700PlusMidpointP001Radius2571,
      corrC02700PlusMidpointP002Radius2571,
      corrC02700PlusMidpointP003Radius2571,
      corrC02700PlusMidpointP004Radius2571,
      corrC02700PlusMidpointP005Radius2571,
      corrC02700PlusMidpointP006Radius2571,
      corrC02700PlusMidpointP007Radius2571,
      corrC02700PlusMidpointP008Radius2571,
      corrC02700PlusMidpointP009Radius2571,
      corrC02700PlusMidpointP010Radius2571,
      corrC02700PlusMidpointP011Radius2571,
      corrC02700PlusMidpointP012Radius2571,
      corrC02700PlusMidpointP013Radius2571,
      corrC02700PlusMidpointP014Radius2571,
      corrC02700PlusMidpointP015Radius2571,
      corrC02700PlusMidpointP016Radius2571,
      corrC02700PlusMidpointP017Radius2571,
      corrC02700PlusMidpointP018Radius2571,
      corrC02700PlusMidpointP019Radius2571,
      corrC02700PlusMidpointP020Radius2571,
      corrC02700PlusMidpointP021Radius2571,
      corrC02700PlusMidpointP022Radius2571,
      corrC02700PlusMidpointP023Radius2571,
      corrC02700PlusMidpointP024Radius2571,
      corrC02700PlusMidpointP025Radius2571,
      corrC02700PlusMidpointP026Radius2571,
      corrC02700PlusMidpointP027Radius2571,
      corrC02700PlusMidpointP028Radius2571,
      corrC02700PlusMidpointP029Radius2571]

theorem corrC02700PlusSignedMidpointUpper_le2571 :
    signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 corrC02700PlusMidpointPosition2571 ≤
          corrC02700PlusSignedMidpointUpper2571 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrC02700PlusMidpointPosition2571‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrC02700PlusSignedMidpointValue2571 i‖
          +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * corrC02700PlusSignedMidpointError2571 i :=
              by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (corrC02700PlusSignedMidpointExpError2571 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrC02700PlusMidpointPosition2571‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (corrC02700PlusSignedMidpointUnitNorm2571 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrC02700PlusMidpointPosition2571‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 corrC02700PlusSignedMidpointUpper2571
  linarith [corrC02700PlusSignedMidpointSum_norm2571, corrC02700PlusSignedMidpointCharge2571]

theorem corrC02700PlusPhysicalSecond2571 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        corrC02700PlusMidpointPosition2571‖ ≤
      corrC02700PlusSignedMidpointUpper2571 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i)) corrC02700PlusMidpointPosition2571
  exact h.trans corrC02700PlusSignedMidpointUpper_le2571

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrC02700PlusSignedMidpointExpError2571
#print axioms ConnesWeilRH.Dev.corrC02700PlusSignedMidpointSum_eq2571
#print axioms ConnesWeilRH.Dev.corrC02700PlusSignedMidpointCharge2571
#print axioms ConnesWeilRH.Dev.corrC02700PlusSignedMidpointUpper_le2571
#print axioms ConnesWeilRH.Dev.corrC02700PlusPhysicalSecond2571
