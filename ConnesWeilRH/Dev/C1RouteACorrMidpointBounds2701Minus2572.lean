import ConnesWeilRH.Dev.C1RouteACorrMidpointDerivatives2701Minus2572
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem corrC02701MinusMidpoint_triangle2572 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def corrC02701MinusMidpointP000Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP000Radius2572 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrC02701MinusMidpointP000RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP000Factor2572
        corrC02701MinusMidpointP000Center2572) =
        corrC02701MinusMidpointP000Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP000RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP000Rounded2572‖ ≤
          corrC02701MinusMidpointP000Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP000Factor2572
      corrC02701MinusMidpointP000Center2572)
  rw [corrC02701MinusMidpointP000RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP000Factor2572 * embedPair2542
        corrC02701MinusMidpointP000Center2572)
    (embedPair2542 corrC02701MinusMidpointP000Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP000DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP000Factor2572,
      corrC02701MinusMidpointP000Error2572, rounding2542,
      corrC02701MinusMidpointP000Radius2572]

theorem corrC02701MinusMidpointP000DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP000Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP000RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP000Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP000Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP000Rounded2572]

def corrC02701MinusMidpointP001Rounded2572 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP001Radius2572 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02701MinusMidpointP001RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP001Factor2572
        corrC02701MinusMidpointP001Center2572) =
        corrC02701MinusMidpointP001Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP001RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP001Rounded2572‖ ≤
          corrC02701MinusMidpointP001Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP001Factor2572
      corrC02701MinusMidpointP001Center2572)
  rw [corrC02701MinusMidpointP001RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP001Factor2572 * embedPair2542
        corrC02701MinusMidpointP001Center2572)
    (embedPair2542 corrC02701MinusMidpointP001Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP001DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP001Factor2572,
      corrC02701MinusMidpointP001Error2572, rounding2542,
      corrC02701MinusMidpointP001Radius2572]

theorem corrC02701MinusMidpointP001DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP001Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP001RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP001Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP001Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP001Rounded2572]

def corrC02701MinusMidpointP002Rounded2572 : RatPair2542 :=
  (((32161535 : ℚ) /
        1267650600228229401496703205376),
    (((-21426725) : ℚ) /
        1267650600228229401496703205376))

noncomputable def corrC02701MinusMidpointP002Radius2572 : ℝ := ((2199023401881 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02701MinusMidpointP002RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP002Factor2572
        corrC02701MinusMidpointP002Center2572) =
        corrC02701MinusMidpointP002Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP002RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP002Rounded2572‖ ≤
          corrC02701MinusMidpointP002Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP002Factor2572
      corrC02701MinusMidpointP002Center2572)
  rw [corrC02701MinusMidpointP002RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP002Factor2572 * embedPair2542
        corrC02701MinusMidpointP002Center2572)
    (embedPair2542 corrC02701MinusMidpointP002Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP002DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP002Factor2572,
      corrC02701MinusMidpointP002Error2572, rounding2542,
      corrC02701MinusMidpointP002Radius2572]

theorem corrC02701MinusMidpointP002DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP002Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP002RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP002Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP002Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP002Rounded2572]

def corrC02701MinusMidpointP003Rounded2572 : RatPair2542 :=
  (((20793699760847 : ℚ) /
        79228162514264337593543950336),
    ((116620257820633 : ℚ) /
        1267650600228229401496703205376))

noncomputable def corrC02701MinusMidpointP003Radius2572 : ℝ := ((3912682925447 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02701MinusMidpointP003RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP003Factor2572
        corrC02701MinusMidpointP003Center2572) =
        corrC02701MinusMidpointP003Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP003RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP003Rounded2572‖ ≤
          corrC02701MinusMidpointP003Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP003Factor2572
      corrC02701MinusMidpointP003Center2572)
  rw [corrC02701MinusMidpointP003RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP003Factor2572 * embedPair2542
        corrC02701MinusMidpointP003Center2572)
    (embedPair2542 corrC02701MinusMidpointP003Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP003DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP003Factor2572,
      corrC02701MinusMidpointP003Error2572, rounding2542,
      corrC02701MinusMidpointP003Radius2572]

theorem corrC02701MinusMidpointP003DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP003Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP003RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP003Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP003Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP003Rounded2572]

def corrC02701MinusMidpointP004Rounded2572 : RatPair2542 :=
  (((62750675647064755 : ℚ) /
        633825300114114700748351602688),
    (((-25047290589943139) : ℚ) /
        316912650057057350374175801344))

noncomputable def corrC02701MinusMidpointP004Radius2572 : ℝ := ((86581930924447 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem corrC02701MinusMidpointP004RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP004Factor2572
        corrC02701MinusMidpointP004Center2572) =
        corrC02701MinusMidpointP004Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP004RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP004Rounded2572‖ ≤
          corrC02701MinusMidpointP004Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP004Factor2572
      corrC02701MinusMidpointP004Center2572)
  rw [corrC02701MinusMidpointP004RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP004Factor2572 * embedPair2542
        corrC02701MinusMidpointP004Center2572)
    (embedPair2542 corrC02701MinusMidpointP004Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP004DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP004Factor2572,
      corrC02701MinusMidpointP004Error2572, rounding2542,
      corrC02701MinusMidpointP004Radius2572]

theorem corrC02701MinusMidpointP004DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP004Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP004RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP004Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP004Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP004Rounded2572]

def corrC02701MinusMidpointP005Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP005Radius2572 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrC02701MinusMidpointP005RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP005Factor2572
        corrC02701MinusMidpointP005Center2572) =
        corrC02701MinusMidpointP005Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP005RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP005Rounded2572‖ ≤
          corrC02701MinusMidpointP005Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP005Factor2572
      corrC02701MinusMidpointP005Center2572)
  rw [corrC02701MinusMidpointP005RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP005Factor2572 * embedPair2542
        corrC02701MinusMidpointP005Center2572)
    (embedPair2542 corrC02701MinusMidpointP005Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP005DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP005Factor2572,
      corrC02701MinusMidpointP005Error2572, rounding2542,
      corrC02701MinusMidpointP005Radius2572]

theorem corrC02701MinusMidpointP005DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP005Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP005RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP005Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP005Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP005Rounded2572]

def corrC02701MinusMidpointP006Rounded2572 : RatPair2542 :=
  (((3 : ℚ) /
        39614081257132168796771975168),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP006Radius2572 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02701MinusMidpointP006RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP006Factor2572
        corrC02701MinusMidpointP006Center2572) =
        corrC02701MinusMidpointP006Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP006RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP006Rounded2572‖ ≤
          corrC02701MinusMidpointP006Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP006Factor2572
      corrC02701MinusMidpointP006Center2572)
  rw [corrC02701MinusMidpointP006RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP006Factor2572 * embedPair2542
        corrC02701MinusMidpointP006Center2572)
    (embedPair2542 corrC02701MinusMidpointP006Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP006DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP006Factor2572,
      corrC02701MinusMidpointP006Error2572, rounding2542,
      corrC02701MinusMidpointP006Radius2572]

theorem corrC02701MinusMidpointP006DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP006Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP006RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP006Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP006Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP006Rounded2572]

def corrC02701MinusMidpointP007Rounded2572 : RatPair2542 :=
  (((17919443941051 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP007Radius2572 : ℝ := ((2203982738439 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02701MinusMidpointP007RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP007Factor2572
        corrC02701MinusMidpointP007Center2572) =
        corrC02701MinusMidpointP007Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP007RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP007Rounded2572‖ ≤
          corrC02701MinusMidpointP007Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP007Factor2572
      corrC02701MinusMidpointP007Center2572)
  rw [corrC02701MinusMidpointP007RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP007Factor2572 * embedPair2542
        corrC02701MinusMidpointP007Center2572)
    (embedPair2542 corrC02701MinusMidpointP007Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP007DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP007Factor2572,
      corrC02701MinusMidpointP007Error2572, rounding2542,
      corrC02701MinusMidpointP007Radius2572]

theorem corrC02701MinusMidpointP007DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP007Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP007RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP007Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP007Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP007Rounded2572]

def corrC02701MinusMidpointP008Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP008Radius2572 : ℝ := ((549831567975 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrC02701MinusMidpointP008RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP008Factor2572
        corrC02701MinusMidpointP008Center2572) =
        corrC02701MinusMidpointP008Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP008RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP008Rounded2572‖ ≤
          corrC02701MinusMidpointP008Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP008Factor2572
      corrC02701MinusMidpointP008Center2572)
  rw [corrC02701MinusMidpointP008RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP008Factor2572 * embedPair2542
        corrC02701MinusMidpointP008Center2572)
    (embedPair2542 corrC02701MinusMidpointP008Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP008DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP008Factor2572,
      corrC02701MinusMidpointP008Error2572, rounding2542,
      corrC02701MinusMidpointP008Radius2572]

theorem corrC02701MinusMidpointP008DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP008Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP008RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP008Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP008Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP008Rounded2572]

def corrC02701MinusMidpointP009Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP009Radius2572 : ℝ := ((2199326272231 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02701MinusMidpointP009RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP009Factor2572
        corrC02701MinusMidpointP009Center2572) =
        corrC02701MinusMidpointP009Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP009RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP009Rounded2572‖ ≤
          corrC02701MinusMidpointP009Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP009Factor2572
      corrC02701MinusMidpointP009Center2572)
  rw [corrC02701MinusMidpointP009RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP009Factor2572 * embedPair2542
        corrC02701MinusMidpointP009Center2572)
    (embedPair2542 corrC02701MinusMidpointP009Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP009DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP009Factor2572,
      corrC02701MinusMidpointP009Error2572, rounding2542,
      corrC02701MinusMidpointP009Radius2572]

theorem corrC02701MinusMidpointP009DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 := by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP009Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP009RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP009Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP009Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP009Rounded2572]

def corrC02701MinusMidpointP010Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP010Radius2572 : ℝ := ((2199326272423 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02701MinusMidpointP010RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP010Factor2572
        corrC02701MinusMidpointP010Center2572) =
        corrC02701MinusMidpointP010Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP010RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP010Rounded2572‖ ≤
          corrC02701MinusMidpointP010Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP010Factor2572
      corrC02701MinusMidpointP010Center2572)
  rw [corrC02701MinusMidpointP010RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP010Factor2572 * embedPair2542
        corrC02701MinusMidpointP010Center2572)
    (embedPair2542 corrC02701MinusMidpointP010Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP010DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP010Factor2572,
      corrC02701MinusMidpointP010Error2572, rounding2542,
      corrC02701MinusMidpointP010Radius2572]

theorem corrC02701MinusMidpointP010DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP010Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP010RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP010Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP010Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP010Rounded2572]

def corrC02701MinusMidpointP011Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP011Radius2572 : ℝ := ((2199326272551 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02701MinusMidpointP011RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP011Factor2572
        corrC02701MinusMidpointP011Center2572) =
        corrC02701MinusMidpointP011Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP011RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP011Rounded2572‖ ≤
          corrC02701MinusMidpointP011Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP011Factor2572
      corrC02701MinusMidpointP011Center2572)
  rw [corrC02701MinusMidpointP011RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP011Factor2572 * embedPair2542
        corrC02701MinusMidpointP011Center2572)
    (embedPair2542 corrC02701MinusMidpointP011Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP011DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP011Factor2572,
      corrC02701MinusMidpointP011Error2572, rounding2542,
      corrC02701MinusMidpointP011Radius2572]

theorem corrC02701MinusMidpointP011DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP011Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP011RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP011Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP011Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP011Rounded2572]

def corrC02701MinusMidpointP012Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP012Radius2572 : ℝ := ((549831568171 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrC02701MinusMidpointP012RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP012Factor2572
        corrC02701MinusMidpointP012Center2572) =
        corrC02701MinusMidpointP012Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP012RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP012Rounded2572‖ ≤
          corrC02701MinusMidpointP012Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP012Factor2572
      corrC02701MinusMidpointP012Center2572)
  rw [corrC02701MinusMidpointP012RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP012Factor2572 * embedPair2542
        corrC02701MinusMidpointP012Center2572)
    (embedPair2542 corrC02701MinusMidpointP012Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP012DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP012Factor2572,
      corrC02701MinusMidpointP012Error2572, rounding2542,
      corrC02701MinusMidpointP012Radius2572]

theorem corrC02701MinusMidpointP012DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP012Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP012RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP012Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP012Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP012Rounded2572]

def corrC02701MinusMidpointP013Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP013Radius2572 : ℝ := ((549831568201 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrC02701MinusMidpointP013RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP013Factor2572
        corrC02701MinusMidpointP013Center2572) =
        corrC02701MinusMidpointP013Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP013RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP013Rounded2572‖ ≤
          corrC02701MinusMidpointP013Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP013Factor2572
      corrC02701MinusMidpointP013Center2572)
  rw [corrC02701MinusMidpointP013RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP013Factor2572 * embedPair2542
        corrC02701MinusMidpointP013Center2572)
    (embedPair2542 corrC02701MinusMidpointP013Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP013DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP013Factor2572,
      corrC02701MinusMidpointP013Error2572, rounding2542,
      corrC02701MinusMidpointP013Radius2572]

theorem corrC02701MinusMidpointP013DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP013Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP013RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP013Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP013Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP013Rounded2572]

def corrC02701MinusMidpointP014Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP014Radius2572 : ℝ := ((549831568257 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrC02701MinusMidpointP014RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP014Factor2572
        corrC02701MinusMidpointP014Center2572) =
        corrC02701MinusMidpointP014Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP014RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP014Rounded2572‖ ≤
          corrC02701MinusMidpointP014Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP014Factor2572
      corrC02701MinusMidpointP014Center2572)
  rw [corrC02701MinusMidpointP014RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP014Factor2572 * embedPair2542
        corrC02701MinusMidpointP014Center2572)
    (embedPair2542 corrC02701MinusMidpointP014Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP014DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP014Factor2572,
      corrC02701MinusMidpointP014Error2572, rounding2542,
      corrC02701MinusMidpointP014Radius2572]

theorem corrC02701MinusMidpointP014DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP014Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP014RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP014Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP014Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP014Rounded2572]

def corrC02701MinusMidpointP015Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP015Radius2572 : ℝ := ((549831568297 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrC02701MinusMidpointP015RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP015Factor2572
        corrC02701MinusMidpointP015Center2572) =
        corrC02701MinusMidpointP015Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP015RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP015Rounded2572‖ ≤
          corrC02701MinusMidpointP015Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP015Factor2572
      corrC02701MinusMidpointP015Center2572)
  rw [corrC02701MinusMidpointP015RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP015Factor2572 * embedPair2542
        corrC02701MinusMidpointP015Center2572)
    (embedPair2542 corrC02701MinusMidpointP015Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP015DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP015Factor2572,
      corrC02701MinusMidpointP015Error2572, rounding2542,
      corrC02701MinusMidpointP015Radius2572]

theorem corrC02701MinusMidpointP015DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP015Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP015RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP015Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP015Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP015Rounded2572]

def corrC02701MinusMidpointP016Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP016Radius2572 : ℝ := ((274915784163 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem corrC02701MinusMidpointP016RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP016Factor2572
        corrC02701MinusMidpointP016Center2572) =
        corrC02701MinusMidpointP016Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP016RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP016Rounded2572‖ ≤
          corrC02701MinusMidpointP016Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP016Factor2572
      corrC02701MinusMidpointP016Center2572)
  rw [corrC02701MinusMidpointP016RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP016Factor2572 * embedPair2542
        corrC02701MinusMidpointP016Center2572)
    (embedPair2542 corrC02701MinusMidpointP016Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP016DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP016Factor2572,
      corrC02701MinusMidpointP016Error2572, rounding2542,
      corrC02701MinusMidpointP016Radius2572]

theorem corrC02701MinusMidpointP016DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP016Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP016RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP016Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP016Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP016Rounded2572]

def corrC02701MinusMidpointP017Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP017Radius2572 : ℝ := ((2199326273529 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02701MinusMidpointP017RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP017Factor2572
        corrC02701MinusMidpointP017Center2572) =
        corrC02701MinusMidpointP017Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP017RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP017Rounded2572‖ ≤
          corrC02701MinusMidpointP017Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP017Factor2572
      corrC02701MinusMidpointP017Center2572)
  rw [corrC02701MinusMidpointP017RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP017Factor2572 * embedPair2542
        corrC02701MinusMidpointP017Center2572)
    (embedPair2542 corrC02701MinusMidpointP017Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP017DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP017Factor2572,
      corrC02701MinusMidpointP017Error2572, rounding2542,
      corrC02701MinusMidpointP017Radius2572]

theorem corrC02701MinusMidpointP017DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP017Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP017RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP017Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP017Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP017Rounded2572]

def corrC02701MinusMidpointP018Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP018Radius2572 : ℝ := ((1099663136807 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02701MinusMidpointP018RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP018Factor2572
        corrC02701MinusMidpointP018Center2572) =
        corrC02701MinusMidpointP018Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP018RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP018Rounded2572‖ ≤
          corrC02701MinusMidpointP018Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP018Factor2572
      corrC02701MinusMidpointP018Center2572)
  rw [corrC02701MinusMidpointP018RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP018Factor2572 * embedPair2542
        corrC02701MinusMidpointP018Center2572)
    (embedPair2542 corrC02701MinusMidpointP018Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP018DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP018Factor2572,
      corrC02701MinusMidpointP018Error2572, rounding2542,
      corrC02701MinusMidpointP018Radius2572]

theorem corrC02701MinusMidpointP018DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP018Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP018RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP018Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP018Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP018Rounded2572]

def corrC02701MinusMidpointP019Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP019Radius2572 : ℝ := ((274915784221 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem corrC02701MinusMidpointP019RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP019Factor2572
        corrC02701MinusMidpointP019Center2572) =
        corrC02701MinusMidpointP019Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP019RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP019Rounded2572‖ ≤
          corrC02701MinusMidpointP019Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP019Factor2572
      corrC02701MinusMidpointP019Center2572)
  rw [corrC02701MinusMidpointP019RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP019Factor2572 * embedPair2542
        corrC02701MinusMidpointP019Center2572)
    (embedPair2542 corrC02701MinusMidpointP019Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP019DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP019Factor2572,
      corrC02701MinusMidpointP019Error2572, rounding2542,
      corrC02701MinusMidpointP019Radius2572]

theorem corrC02701MinusMidpointP019DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP019Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP019RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP019Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP019Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP019Rounded2572]

def corrC02701MinusMidpointP020Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP020Radius2572 : ℝ := ((2199326273935 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02701MinusMidpointP020RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP020Factor2572
        corrC02701MinusMidpointP020Center2572) =
        corrC02701MinusMidpointP020Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP020RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP020Rounded2572‖ ≤
          corrC02701MinusMidpointP020Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP020Factor2572
      corrC02701MinusMidpointP020Center2572)
  rw [corrC02701MinusMidpointP020RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP020Factor2572 * embedPair2542
        corrC02701MinusMidpointP020Center2572)
    (embedPair2542 corrC02701MinusMidpointP020Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP020DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP020Factor2572,
      corrC02701MinusMidpointP020Error2572, rounding2542,
      corrC02701MinusMidpointP020Radius2572]

theorem corrC02701MinusMidpointP020DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP020Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP020RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP020Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP020Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP020Rounded2572]

def corrC02701MinusMidpointP021Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP021Radius2572 : ℝ := ((1099663137037 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02701MinusMidpointP021RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP021Factor2572
        corrC02701MinusMidpointP021Center2572) =
        corrC02701MinusMidpointP021Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP021RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP021Rounded2572‖ ≤
          corrC02701MinusMidpointP021Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP021Factor2572
      corrC02701MinusMidpointP021Center2572)
  rw [corrC02701MinusMidpointP021RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP021Factor2572 * embedPair2542
        corrC02701MinusMidpointP021Center2572)
    (embedPair2542 corrC02701MinusMidpointP021Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP021DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP021Factor2572,
      corrC02701MinusMidpointP021Error2572, rounding2542,
      corrC02701MinusMidpointP021Radius2572]

theorem corrC02701MinusMidpointP021DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP021Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP021RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP021Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP021Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP021Rounded2572]

def corrC02701MinusMidpointP022Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP022Radius2572 : ℝ := ((1099663137073 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02701MinusMidpointP022RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP022Factor2572
        corrC02701MinusMidpointP022Center2572) =
        corrC02701MinusMidpointP022Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP022RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP022Rounded2572‖ ≤
          corrC02701MinusMidpointP022Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP022Factor2572
      corrC02701MinusMidpointP022Center2572)
  rw [corrC02701MinusMidpointP022RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP022Factor2572 * embedPair2542
        corrC02701MinusMidpointP022Center2572)
    (embedPair2542 corrC02701MinusMidpointP022Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP022DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP022Factor2572,
      corrC02701MinusMidpointP022Error2572, rounding2542,
      corrC02701MinusMidpointP022Radius2572]

theorem corrC02701MinusMidpointP022DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP022Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP022RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP022Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP022Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP022Rounded2572]

def corrC02701MinusMidpointP023Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP023Radius2572 : ℝ := ((2199326274351 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02701MinusMidpointP023RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP023Factor2572
        corrC02701MinusMidpointP023Center2572) =
        corrC02701MinusMidpointP023Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP023RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP023Rounded2572‖ ≤
          corrC02701MinusMidpointP023Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP023Factor2572
      corrC02701MinusMidpointP023Center2572)
  rw [corrC02701MinusMidpointP023RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP023Factor2572 * embedPair2542
        corrC02701MinusMidpointP023Center2572)
    (embedPair2542 corrC02701MinusMidpointP023Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP023DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP023Factor2572,
      corrC02701MinusMidpointP023Error2572, rounding2542,
      corrC02701MinusMidpointP023Radius2572]

theorem corrC02701MinusMidpointP023DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP023Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP023RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP023Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP023Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP023Rounded2572]

def corrC02701MinusMidpointP024Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP024Radius2572 : ℝ := ((1099663137223 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02701MinusMidpointP024RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP024Factor2572
        corrC02701MinusMidpointP024Center2572) =
        corrC02701MinusMidpointP024Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP024RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP024Rounded2572‖ ≤
          corrC02701MinusMidpointP024Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP024Factor2572
      corrC02701MinusMidpointP024Center2572)
  rw [corrC02701MinusMidpointP024RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP024Factor2572 * embedPair2542
        corrC02701MinusMidpointP024Center2572)
    (embedPair2542 corrC02701MinusMidpointP024Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP024DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP024Factor2572,
      corrC02701MinusMidpointP024Error2572, rounding2542,
      corrC02701MinusMidpointP024Radius2572]

theorem corrC02701MinusMidpointP024DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP024Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP024RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP024Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP024Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP024Rounded2572]

def corrC02701MinusMidpointP025Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP025Radius2572 : ℝ := ((2199326274565 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02701MinusMidpointP025RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP025Factor2572
        corrC02701MinusMidpointP025Center2572) =
        corrC02701MinusMidpointP025Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP025RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP025Rounded2572‖ ≤
          corrC02701MinusMidpointP025Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP025Factor2572
      corrC02701MinusMidpointP025Center2572)
  rw [corrC02701MinusMidpointP025RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP025Factor2572 * embedPair2542
        corrC02701MinusMidpointP025Center2572)
    (embedPair2542 corrC02701MinusMidpointP025Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP025DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP025Factor2572,
      corrC02701MinusMidpointP025Error2572, rounding2542,
      corrC02701MinusMidpointP025Radius2572]

theorem corrC02701MinusMidpointP025DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP025Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP025RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP025Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP025Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP025Rounded2572]

def corrC02701MinusMidpointP026Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP026Radius2572 : ℝ := ((1099663137343 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02701MinusMidpointP026RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP026Factor2572
        corrC02701MinusMidpointP026Center2572) =
        corrC02701MinusMidpointP026Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP026RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP026Rounded2572‖ ≤
          corrC02701MinusMidpointP026Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP026Factor2572
      corrC02701MinusMidpointP026Center2572)
  rw [corrC02701MinusMidpointP026RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP026Factor2572 * embedPair2542
        corrC02701MinusMidpointP026Center2572)
    (embedPair2542 corrC02701MinusMidpointP026Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP026DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP026Factor2572,
      corrC02701MinusMidpointP026Error2572, rounding2542,
      corrC02701MinusMidpointP026Radius2572]

theorem corrC02701MinusMidpointP026DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP026Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP026RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP026Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP026Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP026Rounded2572]

def corrC02701MinusMidpointP027Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP027Radius2572 : ℝ := ((2199326274861 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02701MinusMidpointP027RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP027Factor2572
        corrC02701MinusMidpointP027Center2572) =
        corrC02701MinusMidpointP027Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP027RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP027Rounded2572‖ ≤
          corrC02701MinusMidpointP027Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP027Factor2572
      corrC02701MinusMidpointP027Center2572)
  rw [corrC02701MinusMidpointP027RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP027Factor2572 * embedPair2542
        corrC02701MinusMidpointP027Center2572)
    (embedPair2542 corrC02701MinusMidpointP027Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP027DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP027Factor2572,
      corrC02701MinusMidpointP027Error2572, rounding2542,
      corrC02701MinusMidpointP027Radius2572]

theorem corrC02701MinusMidpointP027DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP027Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP027RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP027Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP027Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP027Rounded2572]

def corrC02701MinusMidpointP028Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP028Radius2572 : ℝ := ((1099663137465 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrC02701MinusMidpointP028RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP028Factor2572
        corrC02701MinusMidpointP028Center2572) =
        corrC02701MinusMidpointP028Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP028RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP028Rounded2572‖ ≤
          corrC02701MinusMidpointP028Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP028Factor2572
      corrC02701MinusMidpointP028Center2572)
  rw [corrC02701MinusMidpointP028RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP028Factor2572 * embedPair2542
        corrC02701MinusMidpointP028Center2572)
    (embedPair2542 corrC02701MinusMidpointP028Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP028DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP028Factor2572,
      corrC02701MinusMidpointP028Error2572, rounding2542,
      corrC02701MinusMidpointP028Radius2572]

theorem corrC02701MinusMidpointP028DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP028Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP028RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP028Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP028Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP028Rounded2572]

def corrC02701MinusMidpointP029Rounded2572 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrC02701MinusMidpointP029Radius2572 : ℝ := ((2199326275035 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrC02701MinusMidpointP029RoundCompute2572 :
    pairRound2542 (pairMul2542 corrC02701MinusMidpointP029Factor2572
        corrC02701MinusMidpointP029Center2572) =
        corrC02701MinusMidpointP029Rounded2572 := by
  cbv

theorem corrC02701MinusMidpointP029RoundedError2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02701MinusMidpointPosition2572 -
      embedPair2542 corrC02701MinusMidpointP029Rounded2572‖ ≤
          corrC02701MinusMidpointP029Radius2572 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrC02701MinusMidpointP029Factor2572
      corrC02701MinusMidpointP029Center2572)
  rw [corrC02701MinusMidpointP029RoundCompute2572, embedPair_mul2542] at hr
  have h := (corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP029Factor2572 * embedPair2542
        corrC02701MinusMidpointP029Center2572)
    (embedPair2542 corrC02701MinusMidpointP029Rounded2572)).trans (add_le_add
        corrC02701MinusMidpointP029DerivativeError2572 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrC02701MinusMidpointP029Factor2572,
      corrC02701MinusMidpointP029Error2572, rounding2542,
      corrC02701MinusMidpointP029Radius2572]

theorem corrC02701MinusMidpointP029DerivativeNorm2572 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  have h := corrC02701MinusMidpoint_triangle2572
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrC02701MinusMidpointPosition2572)
    (embedPair2542 corrC02701MinusMidpointP029Rounded2572) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrC02701MinusMidpointP029RoundedError2572
      (embedPair_magnitude2542
      corrC02701MinusMidpointP029Rounded2572))
  apply h'.trans
  norm_num [corrC02701MinusMidpointP029Radius2572, pairMagnitude2542,
      corrC02701MinusMidpointP029Rounded2572]

noncomputable def corrC02701MinusSignedMidpointValue2572 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 corrC02701MinusMidpointP000Rounded2572
  | 1 => embedPair2542 corrC02701MinusMidpointP001Rounded2572
  | 2 => embedPair2542 corrC02701MinusMidpointP002Rounded2572
  | 3 => embedPair2542 corrC02701MinusMidpointP003Rounded2572
  | 4 => embedPair2542 corrC02701MinusMidpointP004Rounded2572
  | 5 => embedPair2542 corrC02701MinusMidpointP005Rounded2572
  | 6 => embedPair2542 corrC02701MinusMidpointP006Rounded2572
  | 7 => embedPair2542 corrC02701MinusMidpointP007Rounded2572
  | 8 => embedPair2542 corrC02701MinusMidpointP008Rounded2572
  | 9 => embedPair2542 corrC02701MinusMidpointP009Rounded2572
  | 10 => embedPair2542 corrC02701MinusMidpointP010Rounded2572
  | 11 => embedPair2542 corrC02701MinusMidpointP011Rounded2572
  | 12 => embedPair2542 corrC02701MinusMidpointP012Rounded2572
  | 13 => embedPair2542 corrC02701MinusMidpointP013Rounded2572
  | 14 => embedPair2542 corrC02701MinusMidpointP014Rounded2572
  | 15 => embedPair2542 corrC02701MinusMidpointP015Rounded2572
  | 16 => embedPair2542 corrC02701MinusMidpointP016Rounded2572
  | 17 => embedPair2542 corrC02701MinusMidpointP017Rounded2572
  | 18 => embedPair2542 corrC02701MinusMidpointP018Rounded2572
  | 19 => embedPair2542 corrC02701MinusMidpointP019Rounded2572
  | 20 => embedPair2542 corrC02701MinusMidpointP020Rounded2572
  | 21 => embedPair2542 corrC02701MinusMidpointP021Rounded2572
  | 22 => embedPair2542 corrC02701MinusMidpointP022Rounded2572
  | 23 => embedPair2542 corrC02701MinusMidpointP023Rounded2572
  | 24 => embedPair2542 corrC02701MinusMidpointP024Rounded2572
  | 25 => embedPair2542 corrC02701MinusMidpointP025Rounded2572
  | 26 => embedPair2542 corrC02701MinusMidpointP026Rounded2572
  | 27 => embedPair2542 corrC02701MinusMidpointP027Rounded2572
  | 28 => embedPair2542 corrC02701MinusMidpointP028Rounded2572
  | 29 => embedPair2542 corrC02701MinusMidpointP029Rounded2572
  | _ => 0

noncomputable def corrC02701MinusSignedMidpointError2572 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => corrC02701MinusMidpointP000Radius2572
  | 1 => corrC02701MinusMidpointP001Radius2572
  | 2 => corrC02701MinusMidpointP002Radius2572
  | 3 => corrC02701MinusMidpointP003Radius2572
  | 4 => corrC02701MinusMidpointP004Radius2572
  | 5 => corrC02701MinusMidpointP005Radius2572
  | 6 => corrC02701MinusMidpointP006Radius2572
  | 7 => corrC02701MinusMidpointP007Radius2572
  | 8 => corrC02701MinusMidpointP008Radius2572
  | 9 => corrC02701MinusMidpointP009Radius2572
  | 10 => corrC02701MinusMidpointP010Radius2572
  | 11 => corrC02701MinusMidpointP011Radius2572
  | 12 => corrC02701MinusMidpointP012Radius2572
  | 13 => corrC02701MinusMidpointP013Radius2572
  | 14 => corrC02701MinusMidpointP014Radius2572
  | 15 => corrC02701MinusMidpointP015Radius2572
  | 16 => corrC02701MinusMidpointP016Radius2572
  | 17 => corrC02701MinusMidpointP017Radius2572
  | 18 => corrC02701MinusMidpointP018Radius2572
  | 19 => corrC02701MinusMidpointP019Radius2572
  | 20 => corrC02701MinusMidpointP020Radius2572
  | 21 => corrC02701MinusMidpointP021Radius2572
  | 22 => corrC02701MinusMidpointP022Radius2572
  | 23 => corrC02701MinusMidpointP023Radius2572
  | 24 => corrC02701MinusMidpointP024Radius2572
  | 25 => corrC02701MinusMidpointP025Radius2572
  | 26 => corrC02701MinusMidpointP026Radius2572
  | 27 => corrC02701MinusMidpointP027Radius2572
  | 28 => corrC02701MinusMidpointP028Radius2572
  | 29 => corrC02701MinusMidpointP029Radius2572
  | _ => 0

theorem corrC02701MinusSignedMidpointExpError2572 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrC02701MinusMidpointPosition2572 -
        corrC02701MinusSignedMidpointValue2572 i‖ ≤ corrC02701MinusSignedMidpointError2572 i := by
  fin_cases i
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP000RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP001RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP002RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP003RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP004RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP005RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP006RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP007RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP008RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP009RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP010RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP011RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP012RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP013RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP014RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP015RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP016RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP017RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP018RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP019RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP020RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP021RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP022RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP023RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP024RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP025RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP026RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP027RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP028RoundedError2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP029RoundedError2572

theorem corrC02701MinusSignedMidpointUnitNorm2572 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrC02701MinusMidpointPosition2572‖ ≤ 1 :=
        by
  fin_cases i
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP000DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP001DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP002DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP003DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP004DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP005DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP006DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP007DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP008DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP009DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP010DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP011DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP012DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP013DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP014DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP015DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP016DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP017DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP018DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP019DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP020DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP021DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP022DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP023DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP024DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP025DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP026DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP027DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP028DerivativeNorm2572
  · simpa only [corrC02701MinusSignedMidpointValue2572, corrC02701MinusSignedMidpointError2572]
      using
      corrC02701MinusMidpointP029DerivativeNorm2572

noncomputable def corrC02701MinusSignedMidpointSum2572 : ℂ := ⟨(((-(((32267503170715 * 10^40
        + 5710851117250853659625048574732664703799) * 10^40
        + 541154653107988326188044088996627597356) * 10^40
        + 7826373792698280150193823251913816892273)) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888)),
    (((((6821630589442 * 10^40
        + 3859817616847725914382775108827599990859) * 10^40
        + 9154925718405362405611071442851848512733) * 10^40
        + 445830888307933690332261448856129304029) : ℝ) /
        (((709803441694 * 10^40
        + 9286040520740311406294280797278912962090) * 10^40
        + 4324364277263734305479824015949823344796) * 10^40
        + 2659731992932150006119314388217384402944))⟩

noncomputable def corrC02701MinusSignedMidpointUpper2572 : ℝ := ((616953807 : ℝ) /
        25000000)

theorem corrC02701MinusSignedMidpointSum_eq2572 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * corrC02701MinusSignedMidpointValue2572 i) =
      corrC02701MinusSignedMidpointSum2572 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        corrC02701MinusSignedMidpointValue2572,
      corrC02701MinusSignedMidpointSum2572, embedPair2542, corrC02701MinusMidpointP000Rounded2572,
      corrC02701MinusMidpointP001Rounded2572,
      corrC02701MinusMidpointP002Rounded2572,
      corrC02701MinusMidpointP003Rounded2572,
      corrC02701MinusMidpointP004Rounded2572,
      corrC02701MinusMidpointP005Rounded2572,
      corrC02701MinusMidpointP006Rounded2572,
      corrC02701MinusMidpointP007Rounded2572,
      corrC02701MinusMidpointP008Rounded2572,
      corrC02701MinusMidpointP009Rounded2572,
      corrC02701MinusMidpointP010Rounded2572,
      corrC02701MinusMidpointP011Rounded2572,
      corrC02701MinusMidpointP012Rounded2572,
      corrC02701MinusMidpointP013Rounded2572,
      corrC02701MinusMidpointP014Rounded2572,
      corrC02701MinusMidpointP015Rounded2572,
      corrC02701MinusMidpointP016Rounded2572,
      corrC02701MinusMidpointP017Rounded2572,
      corrC02701MinusMidpointP018Rounded2572,
      corrC02701MinusMidpointP019Rounded2572,
      corrC02701MinusMidpointP020Rounded2572,
      corrC02701MinusMidpointP021Rounded2572,
      corrC02701MinusMidpointP022Rounded2572,
      corrC02701MinusMidpointP023Rounded2572,
      corrC02701MinusMidpointP024Rounded2572,
      corrC02701MinusMidpointP025Rounded2572,
      corrC02701MinusMidpointP026Rounded2572,
      corrC02701MinusMidpointP027Rounded2572,
      corrC02701MinusMidpointP028Rounded2572,
      corrC02701MinusMidpointP029Rounded2572, Complex.mul_re, Complex.mul_im]

theorem corrC02701MinusSignedMidpointSum_norm2572 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrC02701MinusSignedMidpointValue2572 i‖ ≤
        ((1233907609 :
        ℝ) /
        50000000) := by
  rw [corrC02701MinusSignedMidpointSum_eq2572]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [corrC02701MinusSignedMidpointSum2572]

theorem corrC02701MinusSignedMidpointCharge2572 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * corrC02701MinusSignedMidpointError2572 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      corrC02701MinusSignedMidpointError2572, corrC02701MinusMidpointP000Radius2572,
      corrC02701MinusMidpointP001Radius2572,
      corrC02701MinusMidpointP002Radius2572,
      corrC02701MinusMidpointP003Radius2572,
      corrC02701MinusMidpointP004Radius2572,
      corrC02701MinusMidpointP005Radius2572,
      corrC02701MinusMidpointP006Radius2572,
      corrC02701MinusMidpointP007Radius2572,
      corrC02701MinusMidpointP008Radius2572,
      corrC02701MinusMidpointP009Radius2572,
      corrC02701MinusMidpointP010Radius2572,
      corrC02701MinusMidpointP011Radius2572,
      corrC02701MinusMidpointP012Radius2572,
      corrC02701MinusMidpointP013Radius2572,
      corrC02701MinusMidpointP014Radius2572,
      corrC02701MinusMidpointP015Radius2572,
      corrC02701MinusMidpointP016Radius2572,
      corrC02701MinusMidpointP017Radius2572,
      corrC02701MinusMidpointP018Radius2572,
      corrC02701MinusMidpointP019Radius2572,
      corrC02701MinusMidpointP020Radius2572,
      corrC02701MinusMidpointP021Radius2572,
      corrC02701MinusMidpointP022Radius2572,
      corrC02701MinusMidpointP023Radius2572,
      corrC02701MinusMidpointP024Radius2572,
      corrC02701MinusMidpointP025Radius2572,
      corrC02701MinusMidpointP026Radius2572,
      corrC02701MinusMidpointP027Radius2572,
      corrC02701MinusMidpointP028Radius2572,
      corrC02701MinusMidpointP029Radius2572]

theorem corrC02701MinusSignedMidpointUpper_le2572 :
    signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 corrC02701MinusMidpointPosition2572 ≤
          corrC02701MinusSignedMidpointUpper2572 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrC02701MinusMidpointPosition2572‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrC02701MinusSignedMidpointValue2572 i‖
          +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * corrC02701MinusSignedMidpointError2572 i :=
              by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (corrC02701MinusSignedMidpointExpError2572 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrC02701MinusMidpointPosition2572‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (corrC02701MinusSignedMidpointUnitNorm2572 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrC02701MinusMidpointPosition2572‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 corrC02701MinusSignedMidpointUpper2572
  linarith [corrC02701MinusSignedMidpointSum_norm2572, corrC02701MinusSignedMidpointCharge2572]

theorem corrC02701MinusPhysicalSecond2572 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        corrC02701MinusMidpointPosition2572‖ ≤
      corrC02701MinusSignedMidpointUpper2572 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        corrC02701MinusMidpointPosition2572
  exact h.trans corrC02701MinusSignedMidpointUpper_le2572

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrC02701MinusSignedMidpointExpError2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusSignedMidpointSum_eq2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusSignedMidpointCharge2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusSignedMidpointUpper_le2572
#print axioms ConnesWeilRH.Dev.corrC02701MinusPhysicalSecond2572
