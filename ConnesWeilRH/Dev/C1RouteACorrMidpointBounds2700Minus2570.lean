import ConnesWeilRH.Dev.C1RouteACorrMidpointDerivatives2570
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem corrC02700MinusMidpoint_triangle2570 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def corrC02700MinusMidpointP000Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP000Radius2570 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrC02700MinusMidpointP000RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP000Factor2570
        corrC02700MinusMidpointP000Center2570) =
        corrC02700MinusMidpointP000Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP000RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP000Rounded2570‖ ≤
          corrC02700MinusMidpointP000Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP000Factor2570
      corrC02700MinusMidpointP000Center2570)
  rw [corrC02700MinusMidpointP000RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP000Factor2570 * embedPair2542
        corrC02700MinusMidpointP000Center2570)
    (embedPair2542 corrC02700MinusMidpointP000Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP000DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP000Factor2570,
      corrC02700MinusMidpointP000Error2570, rounding2542,
      corrC02700MinusMidpointP000Radius2570]

theorem corrC02700MinusMidpointP000DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 := by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP000Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP000RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP000Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP000Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP000Rounded2570]

def corrC02700MinusMidpointP001Rounded2570 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP001Radius2570 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP001RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP001Factor2570
        corrC02700MinusMidpointP001Center2570) =
        corrC02700MinusMidpointP001Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP001RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP001Rounded2570‖ ≤
          corrC02700MinusMidpointP001Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP001Factor2570
      corrC02700MinusMidpointP001Center2570)
  rw [corrC02700MinusMidpointP001RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP001Factor2570 * embedPair2542
        corrC02700MinusMidpointP001Center2570)
    (embedPair2542 corrC02700MinusMidpointP001Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP001DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP001Factor2570,
      corrC02700MinusMidpointP001Error2570, rounding2542,
      corrC02700MinusMidpointP001Radius2570]

theorem corrC02700MinusMidpointP001DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 := by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP001Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP001RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP001Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP001Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP001Rounded2570]

def corrC02700MinusMidpointP002Rounded2570 : RatPair2542 :=
  (((14734133 : ℚ) /
        633825300114114700748351602688),
    (((-21944745) : ℚ) /
        1267650600228229401496703205376))

noncomputable def corrC02700MinusMidpointP002Radius2570 : ℝ := ((2199023393955 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP002RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP002Factor2570
        corrC02700MinusMidpointP002Center2570) =
        corrC02700MinusMidpointP002Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP002RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP002Rounded2570‖ ≤
          corrC02700MinusMidpointP002Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP002Factor2570
      corrC02700MinusMidpointP002Center2570)
  rw [corrC02700MinusMidpointP002RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP002Factor2570 * embedPair2542
        corrC02700MinusMidpointP002Center2570)
    (embedPair2542 corrC02700MinusMidpointP002Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP002DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP002Factor2570,
      corrC02700MinusMidpointP002Error2570, rounding2542,
      corrC02700MinusMidpointP002Radius2570]

theorem corrC02700MinusMidpointP002DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 := by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP002Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP002RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP002Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP002Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP002Rounded2570]

def corrC02700MinusMidpointP003Rounded2570 : RatPair2542 :=
  (((332377269281621 : ℚ) /
        1267650600228229401496703205376),
    ((48890259578371 : ℚ) /
        633825300114114700748351602688))

noncomputable def corrC02700MinusMidpointP003Radius2570 : ℝ := ((3870929946619 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP003RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP003Factor2570
        corrC02700MinusMidpointP003Center2570) =
        corrC02700MinusMidpointP003Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP003RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP003Rounded2570‖ ≤
          corrC02700MinusMidpointP003Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP003Factor2570
      corrC02700MinusMidpointP003Center2570)
  rw [corrC02700MinusMidpointP003RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP003Factor2570 * embedPair2542
        corrC02700MinusMidpointP003Center2570)
    (embedPair2542 corrC02700MinusMidpointP003Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP003DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP003Factor2570,
      corrC02700MinusMidpointP003Error2570, rounding2542,
      corrC02700MinusMidpointP003Radius2570]

theorem corrC02700MinusMidpointP003DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 := by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP003Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP003RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP003Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP003Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP003Rounded2570]

def corrC02700MinusMidpointP004Rounded2570 : RatPair2542 :=
  (((129302948675881649 : ℚ) /
        1267650600228229401496703205376),
    (((-92927573240012739) : ℚ) /
        1267650600228229401496703205376))

noncomputable def corrC02700MinusMidpointP004Radius2570 : ℝ := ((681893315266257 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP004RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP004Factor2570
        corrC02700MinusMidpointP004Center2570) =
        corrC02700MinusMidpointP004Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP004RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP004Rounded2570‖ ≤
          corrC02700MinusMidpointP004Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP004Factor2570
      corrC02700MinusMidpointP004Center2570)
  rw [corrC02700MinusMidpointP004RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP004Factor2570 * embedPair2542
        corrC02700MinusMidpointP004Center2570)
    (embedPair2542 corrC02700MinusMidpointP004Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP004DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP004Factor2570,
      corrC02700MinusMidpointP004Error2570, rounding2542,
      corrC02700MinusMidpointP004Radius2570]

theorem corrC02700MinusMidpointP004DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 := by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP004Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP004RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP004Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP004Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP004Rounded2570]

def corrC02700MinusMidpointP005Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP005Radius2570 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrC02700MinusMidpointP005RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP005Factor2570
        corrC02700MinusMidpointP005Center2570) =
        corrC02700MinusMidpointP005Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP005RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP005Rounded2570‖ ≤
          corrC02700MinusMidpointP005Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP005Factor2570
      corrC02700MinusMidpointP005Center2570)
  rw [corrC02700MinusMidpointP005RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP005Factor2570 * embedPair2542
        corrC02700MinusMidpointP005Center2570)
    (embedPair2542 corrC02700MinusMidpointP005Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP005DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP005Factor2570,
      corrC02700MinusMidpointP005Error2570, rounding2542,
      corrC02700MinusMidpointP005Radius2570]

theorem corrC02700MinusMidpointP005DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 := by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP005Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP005RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP005Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP005Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP005Rounded2570]

def corrC02700MinusMidpointP006Rounded2570 : RatPair2542 :=
  (((11 : ℚ) /
        158456325028528675187087900672),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP006Radius2570 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP006RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP006Factor2570
        corrC02700MinusMidpointP006Center2570) =
        corrC02700MinusMidpointP006Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP006RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP006Rounded2570‖ ≤
          corrC02700MinusMidpointP006Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP006Factor2570
      corrC02700MinusMidpointP006Center2570)
  rw [corrC02700MinusMidpointP006RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP006Factor2570 * embedPair2542
        corrC02700MinusMidpointP006Center2570)
    (embedPair2542 corrC02700MinusMidpointP006Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP006DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP006Factor2570,
      corrC02700MinusMidpointP006Error2570, rounding2542,
      corrC02700MinusMidpointP006Radius2570]

theorem corrC02700MinusMidpointP006DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 := by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP006Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP006RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP006Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP006Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP006Rounded2570]

def corrC02700MinusMidpointP007Rounded2570 : RatPair2542 :=
  (((17651353462899 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP007Radius2570 : ℝ := ((1101954945631 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02700MinusMidpointP007RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP007Factor2570
        corrC02700MinusMidpointP007Center2570) =
        corrC02700MinusMidpointP007Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP007RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP007Rounded2570‖ ≤
          corrC02700MinusMidpointP007Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP007Factor2570
      corrC02700MinusMidpointP007Center2570)
  rw [corrC02700MinusMidpointP007RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP007Factor2570 * embedPair2542
        corrC02700MinusMidpointP007Center2570)
    (embedPair2542 corrC02700MinusMidpointP007Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP007DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP007Factor2570,
      corrC02700MinusMidpointP007Error2570, rounding2542,
      corrC02700MinusMidpointP007Radius2570]

theorem corrC02700MinusMidpointP007DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 := by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP007Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP007RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP007Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP007Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP007Rounded2570]

def corrC02700MinusMidpointP008Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP008Radius2570 : ℝ := ((2223573723861 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP008RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP008Factor2570
        corrC02700MinusMidpointP008Center2570) =
        corrC02700MinusMidpointP008Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP008RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP008Rounded2570‖ ≤
          corrC02700MinusMidpointP008Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP008Factor2570
      corrC02700MinusMidpointP008Center2570)
  rw [corrC02700MinusMidpointP008RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP008Factor2570 * embedPair2542
        corrC02700MinusMidpointP008Center2570)
    (embedPair2542 corrC02700MinusMidpointP008Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP008DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP008Factor2570,
      corrC02700MinusMidpointP008Error2570, rounding2542,
      corrC02700MinusMidpointP008Radius2570]

theorem corrC02700MinusMidpointP008DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 := by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP008Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP008RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP008Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP008Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP008Rounded2570]

def corrC02700MinusMidpointP009Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP009Radius2570 : ℝ := ((2223573726841 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP009RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP009Factor2570
        corrC02700MinusMidpointP009Center2570) =
        corrC02700MinusMidpointP009Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP009RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP009Rounded2570‖ ≤
          corrC02700MinusMidpointP009Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP009Factor2570
      corrC02700MinusMidpointP009Center2570)
  rw [corrC02700MinusMidpointP009RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP009Factor2570 * embedPair2542
        corrC02700MinusMidpointP009Center2570)
    (embedPair2542 corrC02700MinusMidpointP009Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP009DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP009Factor2570,
      corrC02700MinusMidpointP009Error2570, rounding2542,
      corrC02700MinusMidpointP009Radius2570]

theorem corrC02700MinusMidpointP009DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 := by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP009Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP009RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP009Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP009Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP009Rounded2570]

def corrC02700MinusMidpointP010Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP010Radius2570 : ℝ := ((277946716071 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem corrC02700MinusMidpointP010RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP010Factor2570
        corrC02700MinusMidpointP010Center2570) =
        corrC02700MinusMidpointP010Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP010RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP010Rounded2570‖ ≤
          corrC02700MinusMidpointP010Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP010Factor2570
      corrC02700MinusMidpointP010Center2570)
  rw [corrC02700MinusMidpointP010RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP010Factor2570 * embedPair2542
        corrC02700MinusMidpointP010Center2570)
    (embedPair2542 corrC02700MinusMidpointP010Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP010DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP010Factor2570,
      corrC02700MinusMidpointP010Error2570, rounding2542,
      corrC02700MinusMidpointP010Radius2570]

theorem corrC02700MinusMidpointP010DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP010Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP010RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP010Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP010Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP010Rounded2570]

def corrC02700MinusMidpointP011Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP011Radius2570 : ℝ := ((2223573729719 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP011RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP011Factor2570
        corrC02700MinusMidpointP011Center2570) =
        corrC02700MinusMidpointP011Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP011RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP011Rounded2570‖ ≤
          corrC02700MinusMidpointP011Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP011Factor2570
      corrC02700MinusMidpointP011Center2570)
  rw [corrC02700MinusMidpointP011RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP011Factor2570 * embedPair2542
        corrC02700MinusMidpointP011Center2570)
    (embedPair2542 corrC02700MinusMidpointP011Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP011DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP011Factor2570,
      corrC02700MinusMidpointP011Error2570, rounding2542,
      corrC02700MinusMidpointP011Radius2570]

theorem corrC02700MinusMidpointP011DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP011Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP011RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP011Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP011Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP011Rounded2570]

def corrC02700MinusMidpointP012Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP012Radius2570 : ℝ := ((2223573730911 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP012RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP012Factor2570
        corrC02700MinusMidpointP012Center2570) =
        corrC02700MinusMidpointP012Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP012RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP012Rounded2570‖ ≤
          corrC02700MinusMidpointP012Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP012Factor2570
      corrC02700MinusMidpointP012Center2570)
  rw [corrC02700MinusMidpointP012RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP012Factor2570 * embedPair2542
        corrC02700MinusMidpointP012Center2570)
    (embedPair2542 corrC02700MinusMidpointP012Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP012DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP012Factor2570,
      corrC02700MinusMidpointP012Error2570, rounding2542,
      corrC02700MinusMidpointP012Radius2570]

theorem corrC02700MinusMidpointP012DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP012Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP012RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP012Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP012Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP012Rounded2570]

def corrC02700MinusMidpointP013Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP013Radius2570 : ℝ := ((2223573731997 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP013RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP013Factor2570
        corrC02700MinusMidpointP013Center2570) =
        corrC02700MinusMidpointP013Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP013RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP013Rounded2570‖ ≤
          corrC02700MinusMidpointP013Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP013Factor2570
      corrC02700MinusMidpointP013Center2570)
  rw [corrC02700MinusMidpointP013RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP013Factor2570 * embedPair2542
        corrC02700MinusMidpointP013Center2570)
    (embedPair2542 corrC02700MinusMidpointP013Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP013DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP013Factor2570,
      corrC02700MinusMidpointP013Error2570, rounding2542,
      corrC02700MinusMidpointP013Radius2570]

theorem corrC02700MinusMidpointP013DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP013Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP013RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP013Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP013Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP013Rounded2570]

def corrC02700MinusMidpointP014Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP014Radius2570 : ℝ := ((1111786867005 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02700MinusMidpointP014RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP014Factor2570
        corrC02700MinusMidpointP014Center2570) =
        corrC02700MinusMidpointP014Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP014RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP014Rounded2570‖ ≤
          corrC02700MinusMidpointP014Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP014Factor2570
      corrC02700MinusMidpointP014Center2570)
  rw [corrC02700MinusMidpointP014RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP014Factor2570 * embedPair2542
        corrC02700MinusMidpointP014Center2570)
    (embedPair2542 corrC02700MinusMidpointP014Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP014DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP014Factor2570,
      corrC02700MinusMidpointP014Error2570, rounding2542,
      corrC02700MinusMidpointP014Radius2570]

theorem corrC02700MinusMidpointP014DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP014Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP014RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP014Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP014Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP014Rounded2570]

def corrC02700MinusMidpointP015Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP015Radius2570 : ℝ := ((2223573735453 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP015RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP015Factor2570
        corrC02700MinusMidpointP015Center2570) =
        corrC02700MinusMidpointP015Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP015RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP015Rounded2570‖ ≤
          corrC02700MinusMidpointP015Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP015Factor2570
      corrC02700MinusMidpointP015Center2570)
  rw [corrC02700MinusMidpointP015RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP015Factor2570 * embedPair2542
        corrC02700MinusMidpointP015Center2570)
    (embedPair2542 corrC02700MinusMidpointP015Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP015DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP015Factor2570,
      corrC02700MinusMidpointP015Error2570, rounding2542,
      corrC02700MinusMidpointP015Radius2570]

theorem corrC02700MinusMidpointP015DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP015Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP015RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP015Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP015Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP015Rounded2570]

def corrC02700MinusMidpointP016Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP016Radius2570 : ℝ := ((2223573736495 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP016RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP016Factor2570
        corrC02700MinusMidpointP016Center2570) =
        corrC02700MinusMidpointP016Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP016RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP016Rounded2570‖ ≤
          corrC02700MinusMidpointP016Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP016Factor2570
      corrC02700MinusMidpointP016Center2570)
  rw [corrC02700MinusMidpointP016RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP016Factor2570 * embedPair2542
        corrC02700MinusMidpointP016Center2570)
    (embedPair2542 corrC02700MinusMidpointP016Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP016DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP016Factor2570,
      corrC02700MinusMidpointP016Error2570, rounding2542,
      corrC02700MinusMidpointP016Radius2570]

theorem corrC02700MinusMidpointP016DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP016Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP016RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP016Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP016Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP016Rounded2570]

def corrC02700MinusMidpointP017Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP017Radius2570 : ℝ := ((2223573738519 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP017RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP017Factor2570
        corrC02700MinusMidpointP017Center2570) =
        corrC02700MinusMidpointP017Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP017RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP017Rounded2570‖ ≤
          corrC02700MinusMidpointP017Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP017Factor2570
      corrC02700MinusMidpointP017Center2570)
  rw [corrC02700MinusMidpointP017RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP017Factor2570 * embedPair2542
        corrC02700MinusMidpointP017Center2570)
    (embedPair2542 corrC02700MinusMidpointP017Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP017DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP017Factor2570,
      corrC02700MinusMidpointP017Error2570, rounding2542,
      corrC02700MinusMidpointP017Radius2570]

theorem corrC02700MinusMidpointP017DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP017Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP017RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP017Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP017Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP017Rounded2570]

def corrC02700MinusMidpointP018Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP018Radius2570 : ℝ := ((2223573739285 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP018RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP018Factor2570
        corrC02700MinusMidpointP018Center2570) =
        corrC02700MinusMidpointP018Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP018RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP018Rounded2570‖ ≤
          corrC02700MinusMidpointP018Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP018Factor2570
      corrC02700MinusMidpointP018Center2570)
  rw [corrC02700MinusMidpointP018RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP018Factor2570 * embedPair2542
        corrC02700MinusMidpointP018Center2570)
    (embedPair2542 corrC02700MinusMidpointP018Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP018DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP018Factor2570,
      corrC02700MinusMidpointP018Error2570, rounding2542,
      corrC02700MinusMidpointP018Radius2570]

theorem corrC02700MinusMidpointP018DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP018Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP018RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP018Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP018Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP018Rounded2570]

def corrC02700MinusMidpointP019Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP019Radius2570 : ℝ := ((555893435167 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrC02700MinusMidpointP019RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP019Factor2570
        corrC02700MinusMidpointP019Center2570) =
        corrC02700MinusMidpointP019Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP019RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP019Rounded2570‖ ≤
          corrC02700MinusMidpointP019Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP019Factor2570
      corrC02700MinusMidpointP019Center2570)
  rw [corrC02700MinusMidpointP019RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP019Factor2570 * embedPair2542
        corrC02700MinusMidpointP019Center2570)
    (embedPair2542 corrC02700MinusMidpointP019Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP019DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP019Factor2570,
      corrC02700MinusMidpointP019Error2570, rounding2542,
      corrC02700MinusMidpointP019Radius2570]

theorem corrC02700MinusMidpointP019DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP019Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP019RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP019Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP019Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP019Rounded2570]

def corrC02700MinusMidpointP020Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP020Radius2570 : ℝ := ((2223573742173 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP020RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP020Factor2570
        corrC02700MinusMidpointP020Center2570) =
        corrC02700MinusMidpointP020Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP020RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP020Rounded2570‖ ≤
          corrC02700MinusMidpointP020Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP020Factor2570
      corrC02700MinusMidpointP020Center2570)
  rw [corrC02700MinusMidpointP020RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP020Factor2570 * embedPair2542
        corrC02700MinusMidpointP020Center2570)
    (embedPair2542 corrC02700MinusMidpointP020Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP020DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP020Factor2570,
      corrC02700MinusMidpointP020Error2570, rounding2542,
      corrC02700MinusMidpointP020Radius2570]

theorem corrC02700MinusMidpointP020DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP020Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP020RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP020Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP020Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP020Rounded2570]

def corrC02700MinusMidpointP021Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP021Radius2570 : ℝ := ((555893435857 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrC02700MinusMidpointP021RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP021Factor2570
        corrC02700MinusMidpointP021Center2570) =
        corrC02700MinusMidpointP021Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP021RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP021Rounded2570‖ ≤
          corrC02700MinusMidpointP021Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP021Factor2570
      corrC02700MinusMidpointP021Center2570)
  rw [corrC02700MinusMidpointP021RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP021Factor2570 * embedPair2542
        corrC02700MinusMidpointP021Center2570)
    (embedPair2542 corrC02700MinusMidpointP021Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP021DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP021Factor2570,
      corrC02700MinusMidpointP021Error2570, rounding2542,
      corrC02700MinusMidpointP021Radius2570]

theorem corrC02700MinusMidpointP021DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP021Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP021RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP021Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP021Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP021Rounded2570]

def corrC02700MinusMidpointP022Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP022Radius2570 : ℝ := ((2223573744071 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP022RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP022Factor2570
        corrC02700MinusMidpointP022Center2570) =
        corrC02700MinusMidpointP022Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP022RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP022Rounded2570‖ ≤
          corrC02700MinusMidpointP022Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP022Factor2570
      corrC02700MinusMidpointP022Center2570)
  rw [corrC02700MinusMidpointP022RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP022Factor2570 * embedPair2542
        corrC02700MinusMidpointP022Center2570)
    (embedPair2542 corrC02700MinusMidpointP022Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP022DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP022Factor2570,
      corrC02700MinusMidpointP022Error2570, rounding2542,
      corrC02700MinusMidpointP022Radius2570]

theorem corrC02700MinusMidpointP022DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP022Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP022RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP022Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP022Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP022Rounded2570]

def corrC02700MinusMidpointP023Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP023Radius2570 : ℝ := ((2223573745923 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP023RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP023Factor2570
        corrC02700MinusMidpointP023Center2570) =
        corrC02700MinusMidpointP023Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP023RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP023Rounded2570‖ ≤
          corrC02700MinusMidpointP023Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP023Factor2570
      corrC02700MinusMidpointP023Center2570)
  rw [corrC02700MinusMidpointP023RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP023Factor2570 * embedPair2542
        corrC02700MinusMidpointP023Center2570)
    (embedPair2542 corrC02700MinusMidpointP023Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP023DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP023Factor2570,
      corrC02700MinusMidpointP023Error2570, rounding2542,
      corrC02700MinusMidpointP023Radius2570]

theorem corrC02700MinusMidpointP023DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP023Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP023RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP023Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP023Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP023Rounded2570]

def corrC02700MinusMidpointP024Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP024Radius2570 : ℝ := ((2223573746775 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP024RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP024Factor2570
        corrC02700MinusMidpointP024Center2570) =
        corrC02700MinusMidpointP024Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP024RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP024Rounded2570‖ ≤
          corrC02700MinusMidpointP024Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP024Factor2570
      corrC02700MinusMidpointP024Center2570)
  rw [corrC02700MinusMidpointP024RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP024Factor2570 * embedPair2542
        corrC02700MinusMidpointP024Center2570)
    (embedPair2542 corrC02700MinusMidpointP024Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP024DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP024Factor2570,
      corrC02700MinusMidpointP024Error2570, rounding2542,
      corrC02700MinusMidpointP024Radius2570]

theorem corrC02700MinusMidpointP024DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP024Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP024RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP024Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP024Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP024Rounded2570]

def corrC02700MinusMidpointP025Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP025Radius2570 : ℝ := ((1111786873921 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02700MinusMidpointP025RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP025Factor2570
        corrC02700MinusMidpointP025Center2570) =
        corrC02700MinusMidpointP025Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP025RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP025Rounded2570‖ ≤
          corrC02700MinusMidpointP025Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP025Factor2570
      corrC02700MinusMidpointP025Center2570)
  rw [corrC02700MinusMidpointP025RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP025Factor2570 * embedPair2542
        corrC02700MinusMidpointP025Center2570)
    (embedPair2542 corrC02700MinusMidpointP025Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP025DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP025Factor2570,
      corrC02700MinusMidpointP025Error2570, rounding2542,
      corrC02700MinusMidpointP025Radius2570]

theorem corrC02700MinusMidpointP025DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP025Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP025RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP025Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP025Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP025Rounded2570]

def corrC02700MinusMidpointP026Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP026Radius2570 : ℝ := ((2223573748933 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP026RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP026Factor2570
        corrC02700MinusMidpointP026Center2570) =
        corrC02700MinusMidpointP026Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP026RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP026Rounded2570‖ ≤
          corrC02700MinusMidpointP026Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP026Factor2570
      corrC02700MinusMidpointP026Center2570)
  rw [corrC02700MinusMidpointP026RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP026Factor2570 * embedPair2542
        corrC02700MinusMidpointP026Center2570)
    (embedPair2542 corrC02700MinusMidpointP026Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP026DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP026Factor2570,
      corrC02700MinusMidpointP026Error2570, rounding2542,
      corrC02700MinusMidpointP026Radius2570]

theorem corrC02700MinusMidpointP026DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP026Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP026RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP026Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP026Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP026Rounded2570]

def corrC02700MinusMidpointP027Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP027Radius2570 : ℝ := ((555893437627 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrC02700MinusMidpointP027RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP027Factor2570
        corrC02700MinusMidpointP027Center2570) =
        corrC02700MinusMidpointP027Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP027RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP027Rounded2570‖ ≤
          corrC02700MinusMidpointP027Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP027Factor2570
      corrC02700MinusMidpointP027Center2570)
  rw [corrC02700MinusMidpointP027RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP027Factor2570 * embedPair2542
        corrC02700MinusMidpointP027Center2570)
    (embedPair2542 corrC02700MinusMidpointP027Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP027DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP027Factor2570,
      corrC02700MinusMidpointP027Error2570, rounding2542,
      corrC02700MinusMidpointP027Radius2570]

theorem corrC02700MinusMidpointP027DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP027Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP027RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP027Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP027Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP027Rounded2570]

def corrC02700MinusMidpointP028Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP028Radius2570 : ℝ := ((2223573751131 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02700MinusMidpointP028RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP028Factor2570
        corrC02700MinusMidpointP028Center2570) =
        corrC02700MinusMidpointP028Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP028RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP028Rounded2570‖ ≤
          corrC02700MinusMidpointP028Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP028Factor2570
      corrC02700MinusMidpointP028Center2570)
  rw [corrC02700MinusMidpointP028RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP028Factor2570 * embedPair2542
        corrC02700MinusMidpointP028Center2570)
    (embedPair2542 corrC02700MinusMidpointP028Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP028DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP028Factor2570,
      corrC02700MinusMidpointP028Error2570, rounding2542,
      corrC02700MinusMidpointP028Radius2570]

theorem corrC02700MinusMidpointP028DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP028Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP028RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP028Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP028Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP028Rounded2570]

def corrC02700MinusMidpointP029Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02700MinusMidpointP029Radius2570 : ℝ := ((138973359505 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem corrC02700MinusMidpointP029RoundCompute2570 :
    pairRound2542 (pairMul2542 corrC02700MinusMidpointP029Factor2570
        corrC02700MinusMidpointP029Center2570) =
        corrC02700MinusMidpointP029Rounded2570 := by
  cbv

theorem corrC02700MinusMidpointP029RoundedError2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02700MinusMidpointPosition2570 -
      embedPair2542 corrC02700MinusMidpointP029Rounded2570‖ ≤
          corrC02700MinusMidpointP029Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02700MinusMidpointP029Factor2570
      corrC02700MinusMidpointP029Center2570)
  rw [corrC02700MinusMidpointP029RoundCompute2570, embedPair_mul2542] at hr
  have h := (corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP029Factor2570 * embedPair2542
        corrC02700MinusMidpointP029Center2570)
    (embedPair2542 corrC02700MinusMidpointP029Rounded2570)).trans (add_le_add
        corrC02700MinusMidpointP029DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02700MinusMidpointP029Factor2570,
      corrC02700MinusMidpointP029Error2570, rounding2542,
      corrC02700MinusMidpointP029Radius2570]

theorem corrC02700MinusMidpointP029DerivativeNorm2570 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  have h := corrC02700MinusMidpoint_triangle2570
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02700MinusMidpointPosition2570)
    (embedPair2542 corrC02700MinusMidpointP029Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02700MinusMidpointP029RoundedError2570
      (embedPair_magnitude2542
      corrC02700MinusMidpointP029Rounded2570))
  apply h'.trans
  norm_num [corrC02700MinusMidpointP029Radius2570, pairMagnitude2542,
      corrC02700MinusMidpointP029Rounded2570]

noncomputable def corrC02700MinusSignedMidpointValue2570 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 corrC02700MinusMidpointP000Rounded2570
  | 1 => embedPair2542 corrC02700MinusMidpointP001Rounded2570
  | 2 => embedPair2542 corrC02700MinusMidpointP002Rounded2570
  | 3 => embedPair2542 corrC02700MinusMidpointP003Rounded2570
  | 4 => embedPair2542 corrC02700MinusMidpointP004Rounded2570
  | 5 => embedPair2542 corrC02700MinusMidpointP005Rounded2570
  | 6 => embedPair2542 corrC02700MinusMidpointP006Rounded2570
  | 7 => embedPair2542 corrC02700MinusMidpointP007Rounded2570
  | 8 => embedPair2542 corrC02700MinusMidpointP008Rounded2570
  | 9 => embedPair2542 corrC02700MinusMidpointP009Rounded2570
  | 10 => embedPair2542 corrC02700MinusMidpointP010Rounded2570
  | 11 => embedPair2542 corrC02700MinusMidpointP011Rounded2570
  | 12 => embedPair2542 corrC02700MinusMidpointP012Rounded2570
  | 13 => embedPair2542 corrC02700MinusMidpointP013Rounded2570
  | 14 => embedPair2542 corrC02700MinusMidpointP014Rounded2570
  | 15 => embedPair2542 corrC02700MinusMidpointP015Rounded2570
  | 16 => embedPair2542 corrC02700MinusMidpointP016Rounded2570
  | 17 => embedPair2542 corrC02700MinusMidpointP017Rounded2570
  | 18 => embedPair2542 corrC02700MinusMidpointP018Rounded2570
  | 19 => embedPair2542 corrC02700MinusMidpointP019Rounded2570
  | 20 => embedPair2542 corrC02700MinusMidpointP020Rounded2570
  | 21 => embedPair2542 corrC02700MinusMidpointP021Rounded2570
  | 22 => embedPair2542 corrC02700MinusMidpointP022Rounded2570
  | 23 => embedPair2542 corrC02700MinusMidpointP023Rounded2570
  | 24 => embedPair2542 corrC02700MinusMidpointP024Rounded2570
  | 25 => embedPair2542 corrC02700MinusMidpointP025Rounded2570
  | 26 => embedPair2542 corrC02700MinusMidpointP026Rounded2570
  | 27 => embedPair2542 corrC02700MinusMidpointP027Rounded2570
  | 28 => embedPair2542 corrC02700MinusMidpointP028Rounded2570
  | 29 => embedPair2542 corrC02700MinusMidpointP029Rounded2570
  | _ => 0

noncomputable def corrC02700MinusSignedMidpointError2570 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => corrC02700MinusMidpointP000Radius2570
  | 1 => corrC02700MinusMidpointP001Radius2570
  | 2 => corrC02700MinusMidpointP002Radius2570
  | 3 => corrC02700MinusMidpointP003Radius2570
  | 4 => corrC02700MinusMidpointP004Radius2570
  | 5 => corrC02700MinusMidpointP005Radius2570
  | 6 => corrC02700MinusMidpointP006Radius2570
  | 7 => corrC02700MinusMidpointP007Radius2570
  | 8 => corrC02700MinusMidpointP008Radius2570
  | 9 => corrC02700MinusMidpointP009Radius2570
  | 10 => corrC02700MinusMidpointP010Radius2570
  | 11 => corrC02700MinusMidpointP011Radius2570
  | 12 => corrC02700MinusMidpointP012Radius2570
  | 13 => corrC02700MinusMidpointP013Radius2570
  | 14 => corrC02700MinusMidpointP014Radius2570
  | 15 => corrC02700MinusMidpointP015Radius2570
  | 16 => corrC02700MinusMidpointP016Radius2570
  | 17 => corrC02700MinusMidpointP017Radius2570
  | 18 => corrC02700MinusMidpointP018Radius2570
  | 19 => corrC02700MinusMidpointP019Radius2570
  | 20 => corrC02700MinusMidpointP020Radius2570
  | 21 => corrC02700MinusMidpointP021Radius2570
  | 22 => corrC02700MinusMidpointP022Radius2570
  | 23 => corrC02700MinusMidpointP023Radius2570
  | 24 => corrC02700MinusMidpointP024Radius2570
  | 25 => corrC02700MinusMidpointP025Radius2570
  | 26 => corrC02700MinusMidpointP026Radius2570
  | 27 => corrC02700MinusMidpointP027Radius2570
  | 28 => corrC02700MinusMidpointP028Radius2570
  | 29 => corrC02700MinusMidpointP029Radius2570
  | _ => 0

theorem corrC02700MinusSignedMidpointExpError2570 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrC02700MinusMidpointPosition2570 -
        corrC02700MinusSignedMidpointValue2570 i‖ ≤ corrC02700MinusSignedMidpointError2570 i := by
  fin_cases i
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP000RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP001RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP002RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP003RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP004RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP005RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP006RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP007RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP008RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP009RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP010RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP011RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP012RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP013RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP014RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP015RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP016RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP017RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP018RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP019RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP020RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP021RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP022RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP023RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP024RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP025RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP026RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP027RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP028RoundedError2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP029RoundedError2570

theorem corrC02700MinusSignedMidpointUnitNorm2570 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrC02700MinusMidpointPosition2570‖ ≤ 1 :=
        by
  fin_cases i
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP000DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP001DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP002DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP003DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP004DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP005DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP006DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP007DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP008DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP009DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP010DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP011DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP012DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP013DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP014DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP015DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP016DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP017DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP018DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP019DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP020DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP021DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP022DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP023DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP024DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP025DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP026DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP027DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP028DerivativeNorm2570
  · simpa only [corrC02700MinusSignedMidpointValue2570, corrC02700MinusSignedMidpointError2570]
      using
      corrC02700MinusMidpointP029DerivativeNorm2570

noncomputable def corrC02700MinusSignedMidpointSum2570 : ℂ := ⟨(((-(((16318900650590 * 10^40
        + 6535128282659263421265664782204576658667) * 10^40
        + 198456699643334958814983571357912912789) * 10^40
        + 9706210929918674928029458886416307598097)) : ℝ) /
        (((709803441694 * 10^40
        + 9286040520740311406294280797278912962090) * 10^40
        + 4324364277263734305479824015949823344796) * 10^40
        + 2659731992932150006119314388217384402944)),
    (((((5946950670951 * 10^40
        + 8287549919450200929831431184474631747492) * 10^40
        + 7024252132940243319091289985458634599546) * 10^40
        + 8128104675838269755283847158911435511201) : ℝ) /
        (((709803441694 * 10^40
        + 9286040520740311406294280797278912962090) * 10^40
        + 4324364277263734305479824015949823344796) * 10^40
        + 2659731992932150006119314388217384402944))⟩

noncomputable def corrC02700MinusSignedMidpointUpper2570 : ℝ := ((305872159 : ℝ) /
        12500000)

theorem corrC02700MinusSignedMidpointSum_eq2570 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * corrC02700MinusSignedMidpointValue2570 i) =
      corrC02700MinusSignedMidpointSum2570 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        corrC02700MinusSignedMidpointValue2570,
      corrC02700MinusSignedMidpointSum2570, embedPair2542, corrC02700MinusMidpointP000Rounded2570,
      corrC02700MinusMidpointP001Rounded2570,
      corrC02700MinusMidpointP002Rounded2570,
      corrC02700MinusMidpointP003Rounded2570,
      corrC02700MinusMidpointP004Rounded2570,
      corrC02700MinusMidpointP005Rounded2570,
      corrC02700MinusMidpointP006Rounded2570,
      corrC02700MinusMidpointP007Rounded2570,
      corrC02700MinusMidpointP008Rounded2570,
      corrC02700MinusMidpointP009Rounded2570,
      corrC02700MinusMidpointP010Rounded2570,
      corrC02700MinusMidpointP011Rounded2570,
      corrC02700MinusMidpointP012Rounded2570,
      corrC02700MinusMidpointP013Rounded2570,
      corrC02700MinusMidpointP014Rounded2570,
      corrC02700MinusMidpointP015Rounded2570,
      corrC02700MinusMidpointP016Rounded2570,
      corrC02700MinusMidpointP017Rounded2570,
      corrC02700MinusMidpointP018Rounded2570,
      corrC02700MinusMidpointP019Rounded2570,
      corrC02700MinusMidpointP020Rounded2570,
      corrC02700MinusMidpointP021Rounded2570,
      corrC02700MinusMidpointP022Rounded2570,
      corrC02700MinusMidpointP023Rounded2570,
      corrC02700MinusMidpointP024Rounded2570,
      corrC02700MinusMidpointP025Rounded2570,
      corrC02700MinusMidpointP026Rounded2570,
      corrC02700MinusMidpointP027Rounded2570,
      corrC02700MinusMidpointP028Rounded2570,
      corrC02700MinusMidpointP029Rounded2570, Complex.mul_re, Complex.mul_im]

theorem corrC02700MinusSignedMidpointSum_norm2570 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrC02700MinusSignedMidpointValue2570 i‖ ≤
        ((1223488631 :
        ℝ) /
        50000000) := by
  rw [corrC02700MinusSignedMidpointSum_eq2570]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [corrC02700MinusSignedMidpointSum2570]

theorem corrC02700MinusSignedMidpointCharge2570 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * corrC02700MinusSignedMidpointError2570 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      corrC02700MinusSignedMidpointError2570, corrC02700MinusMidpointP000Radius2570,
      corrC02700MinusMidpointP001Radius2570,
      corrC02700MinusMidpointP002Radius2570,
      corrC02700MinusMidpointP003Radius2570,
      corrC02700MinusMidpointP004Radius2570,
      corrC02700MinusMidpointP005Radius2570,
      corrC02700MinusMidpointP006Radius2570,
      corrC02700MinusMidpointP007Radius2570,
      corrC02700MinusMidpointP008Radius2570,
      corrC02700MinusMidpointP009Radius2570,
      corrC02700MinusMidpointP010Radius2570,
      corrC02700MinusMidpointP011Radius2570,
      corrC02700MinusMidpointP012Radius2570,
      corrC02700MinusMidpointP013Radius2570,
      corrC02700MinusMidpointP014Radius2570,
      corrC02700MinusMidpointP015Radius2570,
      corrC02700MinusMidpointP016Radius2570,
      corrC02700MinusMidpointP017Radius2570,
      corrC02700MinusMidpointP018Radius2570,
      corrC02700MinusMidpointP019Radius2570,
      corrC02700MinusMidpointP020Radius2570,
      corrC02700MinusMidpointP021Radius2570,
      corrC02700MinusMidpointP022Radius2570,
      corrC02700MinusMidpointP023Radius2570,
      corrC02700MinusMidpointP024Radius2570,
      corrC02700MinusMidpointP025Radius2570,
      corrC02700MinusMidpointP026Radius2570,
      corrC02700MinusMidpointP027Radius2570,
      corrC02700MinusMidpointP028Radius2570,
      corrC02700MinusMidpointP029Radius2570]

theorem corrC02700MinusSignedMidpointUpper_le2570 :
    signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 corrC02700MinusMidpointPosition2570 ≤
          corrC02700MinusSignedMidpointUpper2570 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrC02700MinusMidpointPosition2570‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrC02700MinusSignedMidpointValue2570 i‖
          +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * corrC02700MinusSignedMidpointError2570 i :=
              by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (corrC02700MinusSignedMidpointExpError2570 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrC02700MinusMidpointPosition2570‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (corrC02700MinusSignedMidpointUnitNorm2570 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrC02700MinusMidpointPosition2570‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 corrC02700MinusSignedMidpointUpper2570
  linarith [corrC02700MinusSignedMidpointSum_norm2570, corrC02700MinusSignedMidpointCharge2570]

theorem corrC02700MinusPhysicalSecond2570 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        corrC02700MinusMidpointPosition2570‖ ≤
      corrC02700MinusSignedMidpointUpper2570 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        corrC02700MinusMidpointPosition2570
  exact h.trans corrC02700MinusSignedMidpointUpper_le2570

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrC02700MinusSignedMidpointExpError2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusSignedMidpointSum_eq2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusSignedMidpointCharge2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusSignedMidpointUpper_le2570
#print axioms ConnesWeilRH.Dev.corrC02700MinusPhysicalSecond2570
