import ConnesWeilRH.Dev.C1RouteABatchC02702PlusMidpoint2558

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem batchC02702PlusMidpoint_triangle2558 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def batchC02702PlusMidpointP000Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP000Radius2558 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02702PlusMidpointP000RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP000Factor2558
        batchC02702PlusMidpointP000Center2558) =
        batchC02702PlusMidpointP000Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP000RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP000Rounded2558‖ ≤
          batchC02702PlusMidpointP000Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP000Factor2558
      batchC02702PlusMidpointP000Center2558)
  rw [batchC02702PlusMidpointP000RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP000Factor2558 * embedPair2542
        batchC02702PlusMidpointP000Center2558)
    (embedPair2542 batchC02702PlusMidpointP000Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP000DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP000Factor2558,
      batchC02702PlusMidpointP000Error2558, rounding2542,
      batchC02702PlusMidpointP000Radius2558]

theorem batchC02702PlusMidpointP000DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP000Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP000RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP000Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP000Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP000Rounded2558]

def batchC02702PlusMidpointP001Rounded2558 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP001Radius2558 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702PlusMidpointP001RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP001Factor2558
        batchC02702PlusMidpointP001Center2558) =
        batchC02702PlusMidpointP001Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP001RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP001Rounded2558‖ ≤
          batchC02702PlusMidpointP001Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP001Factor2558
      batchC02702PlusMidpointP001Center2558)
  rw [batchC02702PlusMidpointP001RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP001Factor2558 * embedPair2542
        batchC02702PlusMidpointP001Center2558)
    (embedPair2542 batchC02702PlusMidpointP001Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP001DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP001Factor2558,
      batchC02702PlusMidpointP001Error2558, rounding2542,
      batchC02702PlusMidpointP001Radius2558]

theorem batchC02702PlusMidpointP001DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP001Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP001RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP001Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP001Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP001Rounded2558]

def batchC02702PlusMidpointP002Rounded2558 : RatPair2542 :=
  (((1599523 : ℚ) /
        1267650600228229401496703205376),
    (((-250633) : ℚ) /
        316912650057057350374175801344))

noncomputable def batchC02702PlusMidpointP002Radius2558 : ℝ := ((1099511631493 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02702PlusMidpointP002RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP002Factor2558
        batchC02702PlusMidpointP002Center2558) =
        batchC02702PlusMidpointP002Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP002RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP002Rounded2558‖ ≤
          batchC02702PlusMidpointP002Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP002Factor2558
      batchC02702PlusMidpointP002Center2558)
  rw [batchC02702PlusMidpointP002RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP002Factor2558 * embedPair2542
        batchC02702PlusMidpointP002Center2558)
    (embedPair2542 batchC02702PlusMidpointP002Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP002DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP002Factor2558,
      batchC02702PlusMidpointP002Error2558, rounding2542,
      batchC02702PlusMidpointP002Radius2558]

theorem batchC02702PlusMidpointP002DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP002Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP002RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP002Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP002Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP002Rounded2558]

def batchC02702PlusMidpointP003Rounded2558 : RatPair2542 :=
  (((15550300380119 : ℚ) /
        1267650600228229401496703205376),
    ((694994153315 : ℚ) /
        158456325028528675187087900672))

noncomputable def batchC02702PlusMidpointP003Radius2558 : ℝ := ((2281127867545 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702PlusMidpointP003RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP003Factor2558
        batchC02702PlusMidpointP003Center2558) =
        batchC02702PlusMidpointP003Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP003RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP003Rounded2558‖ ≤
          batchC02702PlusMidpointP003Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP003Factor2558
      batchC02702PlusMidpointP003Center2558)
  rw [batchC02702PlusMidpointP003RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP003Factor2558 * embedPair2542
        batchC02702PlusMidpointP003Center2558)
    (embedPair2542 batchC02702PlusMidpointP003Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP003DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP003Factor2558,
      batchC02702PlusMidpointP003Error2558, rounding2542,
      batchC02702PlusMidpointP003Radius2558]

theorem batchC02702PlusMidpointP003DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP003Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP003RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP003Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP003Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP003Rounded2558]

def batchC02702PlusMidpointP004Rounded2558 : RatPair2542 :=
  (((90293828074637 : ℚ) /
        19807040628566084398385987584),
    (((-144573809547577) : ℚ) /
        39614081257132168796771975168))

noncomputable def batchC02702PlusMidpointP004Radius2558 : ℝ := ((8837307763689 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02702PlusMidpointP004RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP004Factor2558
        batchC02702PlusMidpointP004Center2558) =
        batchC02702PlusMidpointP004Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP004RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP004Rounded2558‖ ≤
          batchC02702PlusMidpointP004Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP004Factor2558
      batchC02702PlusMidpointP004Center2558)
  rw [batchC02702PlusMidpointP004RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP004Factor2558 * embedPair2542
        batchC02702PlusMidpointP004Center2558)
    (embedPair2542 batchC02702PlusMidpointP004Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP004DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP004Factor2558,
      batchC02702PlusMidpointP004Error2558, rounding2542,
      batchC02702PlusMidpointP004Radius2558]

theorem batchC02702PlusMidpointP004DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP004Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP004RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP004Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP004Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP004Rounded2558]

def batchC02702PlusMidpointP005Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP005Radius2558 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02702PlusMidpointP005RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP005Factor2558
        batchC02702PlusMidpointP005Center2558) =
        batchC02702PlusMidpointP005Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP005RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP005Rounded2558‖ ≤
          batchC02702PlusMidpointP005Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP005Factor2558
      batchC02702PlusMidpointP005Center2558)
  rw [batchC02702PlusMidpointP005RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP005Factor2558 * embedPair2542
        batchC02702PlusMidpointP005Center2558)
    (embedPair2542 batchC02702PlusMidpointP005Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP005DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP005Factor2558,
      batchC02702PlusMidpointP005Error2558, rounding2542,
      batchC02702PlusMidpointP005Radius2558]

theorem batchC02702PlusMidpointP005DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP005Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP005RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP005Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP005Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP005Rounded2558]

def batchC02702PlusMidpointP006Rounded2558 : RatPair2542 :=
  (((1 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP006Radius2558 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702PlusMidpointP006RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP006Factor2558
        batchC02702PlusMidpointP006Center2558) =
        batchC02702PlusMidpointP006Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP006RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP006Rounded2558‖ ≤
          batchC02702PlusMidpointP006Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP006Factor2558
      batchC02702PlusMidpointP006Center2558)
  rw [batchC02702PlusMidpointP006RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP006Factor2558 * embedPair2542
        batchC02702PlusMidpointP006Center2558)
    (embedPair2542 batchC02702PlusMidpointP006Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP006DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP006Factor2558,
      batchC02702PlusMidpointP006Error2558, rounding2542,
      batchC02702PlusMidpointP006Radius2558]

theorem batchC02702PlusMidpointP006DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP006Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP006RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP006Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP006Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP006Rounded2558]

def batchC02702PlusMidpointP007Rounded2558 : RatPair2542 :=
  (((957504589221 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP007Radius2558 : ℝ := ((2199301310699 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702PlusMidpointP007RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP007Factor2558
        batchC02702PlusMidpointP007Center2558) =
        batchC02702PlusMidpointP007Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP007RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP007Rounded2558‖ ≤
          batchC02702PlusMidpointP007Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP007Factor2558
      batchC02702PlusMidpointP007Center2558)
  rw [batchC02702PlusMidpointP007RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP007Factor2558 * embedPair2542
        batchC02702PlusMidpointP007Center2558)
    (embedPair2542 batchC02702PlusMidpointP007Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP007DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP007Factor2558,
      batchC02702PlusMidpointP007Error2558, rounding2542,
      batchC02702PlusMidpointP007Radius2558]

theorem batchC02702PlusMidpointP007DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP007Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP007RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP007Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP007Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP007Rounded2558]

def batchC02702PlusMidpointP008Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP008Radius2558 : ℝ := ((549765630729 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02702PlusMidpointP008RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP008Factor2558
        batchC02702PlusMidpointP008Center2558) =
        batchC02702PlusMidpointP008Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP008RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP008Rounded2558‖ ≤
          batchC02702PlusMidpointP008Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP008Factor2558
      batchC02702PlusMidpointP008Center2558)
  rw [batchC02702PlusMidpointP008RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP008Factor2558 * embedPair2542
        batchC02702PlusMidpointP008Center2558)
    (embedPair2542 batchC02702PlusMidpointP008Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP008DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP008Factor2558,
      batchC02702PlusMidpointP008Error2558, rounding2542,
      batchC02702PlusMidpointP008Radius2558]

theorem batchC02702PlusMidpointP008DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP008Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP008RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP008Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP008Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP008Rounded2558]

def batchC02702PlusMidpointP009Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP009Radius2558 : ℝ := ((2199062523035 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702PlusMidpointP009RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP009Factor2558
        batchC02702PlusMidpointP009Center2558) =
        batchC02702PlusMidpointP009Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP009RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP009Rounded2558‖ ≤
          batchC02702PlusMidpointP009Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP009Factor2558
      batchC02702PlusMidpointP009Center2558)
  rw [batchC02702PlusMidpointP009RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP009Factor2558 * embedPair2542
        batchC02702PlusMidpointP009Center2558)
    (embedPair2542 batchC02702PlusMidpointP009Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP009DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP009Factor2558,
      batchC02702PlusMidpointP009Error2558, rounding2542,
      batchC02702PlusMidpointP009Radius2558]

theorem batchC02702PlusMidpointP009DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP009Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP009RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP009Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP009Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP009Rounded2558]

def batchC02702PlusMidpointP010Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP010Radius2558 : ℝ := ((68720703847 : ℝ) /
        (4 * 10^40
        + 3556142965880123323311949751266331066368))

theorem batchC02702PlusMidpointP010RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP010Factor2558
        batchC02702PlusMidpointP010Center2558) =
        batchC02702PlusMidpointP010Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP010RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP010Rounded2558‖ ≤
          batchC02702PlusMidpointP010Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP010Factor2558
      batchC02702PlusMidpointP010Center2558)
  rw [batchC02702PlusMidpointP010RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP010Factor2558 * embedPair2542
        batchC02702PlusMidpointP010Center2558)
    (embedPair2542 batchC02702PlusMidpointP010Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP010DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP010Factor2558,
      batchC02702PlusMidpointP010Error2558, rounding2542,
      batchC02702PlusMidpointP010Radius2558]

theorem batchC02702PlusMidpointP010DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP010Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP010RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP010Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP010Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP010Rounded2558]

def batchC02702PlusMidpointP011Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP011Radius2558 : ℝ := ((1099531261575 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02702PlusMidpointP011RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP011Factor2558
        batchC02702PlusMidpointP011Center2558) =
        batchC02702PlusMidpointP011Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP011RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP011Rounded2558‖ ≤
          batchC02702PlusMidpointP011Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP011Factor2558
      batchC02702PlusMidpointP011Center2558)
  rw [batchC02702PlusMidpointP011RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP011Factor2558 * embedPair2542
        batchC02702PlusMidpointP011Center2558)
    (embedPair2542 batchC02702PlusMidpointP011Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP011DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP011Factor2558,
      batchC02702PlusMidpointP011Error2558, rounding2542,
      batchC02702PlusMidpointP011Radius2558]

theorem batchC02702PlusMidpointP011DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP011Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP011RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP011Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP011Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP011Rounded2558]

def batchC02702PlusMidpointP012Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP012Radius2558 : ℝ := ((1099531261599 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02702PlusMidpointP012RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP012Factor2558
        batchC02702PlusMidpointP012Center2558) =
        batchC02702PlusMidpointP012Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP012RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP012Rounded2558‖ ≤
          batchC02702PlusMidpointP012Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP012Factor2558
      batchC02702PlusMidpointP012Center2558)
  rw [batchC02702PlusMidpointP012RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP012Factor2558 * embedPair2542
        batchC02702PlusMidpointP012Center2558)
    (embedPair2542 batchC02702PlusMidpointP012Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP012DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP012Factor2558,
      batchC02702PlusMidpointP012Error2558, rounding2542,
      batchC02702PlusMidpointP012Radius2558]

theorem batchC02702PlusMidpointP012DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP012Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP012RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP012Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP012Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP012Rounded2558]

def batchC02702PlusMidpointP013Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP013Radius2558 : ℝ := ((2199062523241 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702PlusMidpointP013RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP013Factor2558
        batchC02702PlusMidpointP013Center2558) =
        batchC02702PlusMidpointP013Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP013RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP013Rounded2558‖ ≤
          batchC02702PlusMidpointP013Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP013Factor2558
      batchC02702PlusMidpointP013Center2558)
  rw [batchC02702PlusMidpointP013RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP013Factor2558 * embedPair2542
        batchC02702PlusMidpointP013Center2558)
    (embedPair2542 batchC02702PlusMidpointP013Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP013DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP013Factor2558,
      batchC02702PlusMidpointP013Error2558, rounding2542,
      batchC02702PlusMidpointP013Radius2558]

theorem batchC02702PlusMidpointP013DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP013Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP013RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP013Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP013Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP013Rounded2558]

def batchC02702PlusMidpointP014Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP014Radius2558 : ℝ := ((2199062523321 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702PlusMidpointP014RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP014Factor2558
        batchC02702PlusMidpointP014Center2558) =
        batchC02702PlusMidpointP014Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP014RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP014Rounded2558‖ ≤
          batchC02702PlusMidpointP014Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP014Factor2558
      batchC02702PlusMidpointP014Center2558)
  rw [batchC02702PlusMidpointP014RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP014Factor2558 * embedPair2542
        batchC02702PlusMidpointP014Center2558)
    (embedPair2542 batchC02702PlusMidpointP014Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP014DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP014Factor2558,
      batchC02702PlusMidpointP014Error2558, rounding2542,
      batchC02702PlusMidpointP014Radius2558]

theorem batchC02702PlusMidpointP014DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP014Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP014RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP014Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP014Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP014Rounded2558]

def batchC02702PlusMidpointP015Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP015Radius2558 : ℝ := ((2199062523379 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702PlusMidpointP015RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP015Factor2558
        batchC02702PlusMidpointP015Center2558) =
        batchC02702PlusMidpointP015Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP015RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP015Rounded2558‖ ≤
          batchC02702PlusMidpointP015Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP015Factor2558
      batchC02702PlusMidpointP015Center2558)
  rw [batchC02702PlusMidpointP015RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP015Factor2558 * embedPair2542
        batchC02702PlusMidpointP015Center2558)
    (embedPair2542 batchC02702PlusMidpointP015Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP015DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP015Factor2558,
      batchC02702PlusMidpointP015Error2558, rounding2542,
      batchC02702PlusMidpointP015Radius2558]

theorem batchC02702PlusMidpointP015DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP015Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP015RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP015Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP015Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP015Rounded2558]

def batchC02702PlusMidpointP016Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP016Radius2558 : ℝ := ((2199062523421 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702PlusMidpointP016RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP016Factor2558
        batchC02702PlusMidpointP016Center2558) =
        batchC02702PlusMidpointP016Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP016RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP016Rounded2558‖ ≤
          batchC02702PlusMidpointP016Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP016Factor2558
      batchC02702PlusMidpointP016Center2558)
  rw [batchC02702PlusMidpointP016RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP016Factor2558 * embedPair2542
        batchC02702PlusMidpointP016Center2558)
    (embedPair2542 batchC02702PlusMidpointP016Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP016DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP016Factor2558,
      batchC02702PlusMidpointP016Error2558, rounding2542,
      batchC02702PlusMidpointP016Radius2558]

theorem batchC02702PlusMidpointP016DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP016Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP016RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP016Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP016Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP016Rounded2558]

def batchC02702PlusMidpointP017Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP017Radius2558 : ℝ := ((1099531261751 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02702PlusMidpointP017RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP017Factor2558
        batchC02702PlusMidpointP017Center2558) =
        batchC02702PlusMidpointP017Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP017RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP017Rounded2558‖ ≤
          batchC02702PlusMidpointP017Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP017Factor2558
      batchC02702PlusMidpointP017Center2558)
  rw [batchC02702PlusMidpointP017RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP017Factor2558 * embedPair2542
        batchC02702PlusMidpointP017Center2558)
    (embedPair2542 batchC02702PlusMidpointP017Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP017DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP017Factor2558,
      batchC02702PlusMidpointP017Error2558, rounding2542,
      batchC02702PlusMidpointP017Radius2558]

theorem batchC02702PlusMidpointP017DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP017Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP017RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP017Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP017Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP017Rounded2558]

def batchC02702PlusMidpointP018Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP018Radius2558 : ℝ := ((549765630883 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02702PlusMidpointP018RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP018Factor2558
        batchC02702PlusMidpointP018Center2558) =
        batchC02702PlusMidpointP018Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP018RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP018Rounded2558‖ ≤
          batchC02702PlusMidpointP018Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP018Factor2558
      batchC02702PlusMidpointP018Center2558)
  rw [batchC02702PlusMidpointP018RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP018Factor2558 * embedPair2542
        batchC02702PlusMidpointP018Center2558)
    (embedPair2542 batchC02702PlusMidpointP018Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP018DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP018Factor2558,
      batchC02702PlusMidpointP018Error2558, rounding2542,
      batchC02702PlusMidpointP018Radius2558]

theorem batchC02702PlusMidpointP018DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP018Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP018RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP018Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP018Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP018Rounded2558]

def batchC02702PlusMidpointP019Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP019Radius2558 : ℝ := ((549765630897 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02702PlusMidpointP019RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP019Factor2558
        batchC02702PlusMidpointP019Center2558) =
        batchC02702PlusMidpointP019Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP019RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP019Rounded2558‖ ≤
          batchC02702PlusMidpointP019Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP019Factor2558
      batchC02702PlusMidpointP019Center2558)
  rw [batchC02702PlusMidpointP019RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP019Factor2558 * embedPair2542
        batchC02702PlusMidpointP019Center2558)
    (embedPair2542 batchC02702PlusMidpointP019Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP019DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP019Factor2558,
      batchC02702PlusMidpointP019Error2558, rounding2542,
      batchC02702PlusMidpointP019Radius2558]

theorem batchC02702PlusMidpointP019DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP019Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP019RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP019Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP019Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP019Rounded2558]

def batchC02702PlusMidpointP020Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP020Radius2558 : ℝ := ((8590087983 : ℝ) /
        5444517870735015415413993718908291383296)

theorem batchC02702PlusMidpointP020RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP020Factor2558
        batchC02702PlusMidpointP020Center2558) =
        batchC02702PlusMidpointP020Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP020RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP020Rounded2558‖ ≤
          batchC02702PlusMidpointP020Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP020Factor2558
      batchC02702PlusMidpointP020Center2558)
  rw [batchC02702PlusMidpointP020RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP020Factor2558 * embedPair2542
        batchC02702PlusMidpointP020Center2558)
    (embedPair2542 batchC02702PlusMidpointP020Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP020DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP020Factor2558,
      batchC02702PlusMidpointP020Error2558, rounding2542,
      batchC02702PlusMidpointP020Radius2558]

theorem batchC02702PlusMidpointP020DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP020Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP020RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP020Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP020Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP020Rounded2558]

def batchC02702PlusMidpointP021Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP021Radius2558 : ℝ := ((1099531261849 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02702PlusMidpointP021RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP021Factor2558
        batchC02702PlusMidpointP021Center2558) =
        batchC02702PlusMidpointP021Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP021RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP021Rounded2558‖ ≤
          batchC02702PlusMidpointP021Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP021Factor2558
      batchC02702PlusMidpointP021Center2558)
  rw [batchC02702PlusMidpointP021RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP021Factor2558 * embedPair2542
        batchC02702PlusMidpointP021Center2558)
    (embedPair2542 batchC02702PlusMidpointP021Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP021DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP021Factor2558,
      batchC02702PlusMidpointP021Error2558, rounding2542,
      batchC02702PlusMidpointP021Radius2558]

theorem batchC02702PlusMidpointP021DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP021Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP021RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP021Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP021Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP021Rounded2558]

def batchC02702PlusMidpointP022Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP022Radius2558 : ℝ := ((549765630931 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02702PlusMidpointP022RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP022Factor2558
        batchC02702PlusMidpointP022Center2558) =
        batchC02702PlusMidpointP022Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP022RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP022Rounded2558‖ ≤
          batchC02702PlusMidpointP022Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP022Factor2558
      batchC02702PlusMidpointP022Center2558)
  rw [batchC02702PlusMidpointP022RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP022Factor2558 * embedPair2542
        batchC02702PlusMidpointP022Center2558)
    (embedPair2542 batchC02702PlusMidpointP022Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP022DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP022Factor2558,
      batchC02702PlusMidpointP022Error2558, rounding2542,
      batchC02702PlusMidpointP022Radius2558]

theorem batchC02702PlusMidpointP022DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP022Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP022RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP022Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP022Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP022Rounded2558]

def batchC02702PlusMidpointP023Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP023Radius2558 : ℝ := ((1099531261899 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02702PlusMidpointP023RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP023Factor2558
        batchC02702PlusMidpointP023Center2558) =
        batchC02702PlusMidpointP023Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP023RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP023Rounded2558‖ ≤
          batchC02702PlusMidpointP023Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP023Factor2558
      batchC02702PlusMidpointP023Center2558)
  rw [batchC02702PlusMidpointP023RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP023Factor2558 * embedPair2542
        batchC02702PlusMidpointP023Center2558)
    (embedPair2542 batchC02702PlusMidpointP023Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP023DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP023Factor2558,
      batchC02702PlusMidpointP023Error2558, rounding2542,
      batchC02702PlusMidpointP023Radius2558]

theorem batchC02702PlusMidpointP023DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP023Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP023RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP023Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP023Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP023Rounded2558]

def batchC02702PlusMidpointP024Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP024Radius2558 : ℝ := ((274882815479 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02702PlusMidpointP024RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP024Factor2558
        batchC02702PlusMidpointP024Center2558) =
        batchC02702PlusMidpointP024Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP024RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP024Rounded2558‖ ≤
          batchC02702PlusMidpointP024Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP024Factor2558
      batchC02702PlusMidpointP024Center2558)
  rw [batchC02702PlusMidpointP024RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP024Factor2558 * embedPair2542
        batchC02702PlusMidpointP024Center2558)
    (embedPair2542 batchC02702PlusMidpointP024Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP024DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP024Factor2558,
      batchC02702PlusMidpointP024Error2558, rounding2542,
      batchC02702PlusMidpointP024Radius2558]

theorem batchC02702PlusMidpointP024DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP024Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP024RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP024Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP024Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP024Rounded2558]

def batchC02702PlusMidpointP025Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP025Radius2558 : ℝ := ((2199062523875 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702PlusMidpointP025RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP025Factor2558
        batchC02702PlusMidpointP025Center2558) =
        batchC02702PlusMidpointP025Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP025RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP025Rounded2558‖ ≤
          batchC02702PlusMidpointP025Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP025Factor2558
      batchC02702PlusMidpointP025Center2558)
  rw [batchC02702PlusMidpointP025RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP025Factor2558 * embedPair2542
        batchC02702PlusMidpointP025Center2558)
    (embedPair2542 batchC02702PlusMidpointP025Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP025DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP025Factor2558,
      batchC02702PlusMidpointP025Error2558, rounding2542,
      batchC02702PlusMidpointP025Radius2558]

theorem batchC02702PlusMidpointP025DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP025Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP025RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP025Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP025Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP025Rounded2558]

def batchC02702PlusMidpointP026Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP026Radius2558 : ℝ := ((1099531261959 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02702PlusMidpointP026RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP026Factor2558
        batchC02702PlusMidpointP026Center2558) =
        batchC02702PlusMidpointP026Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP026RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP026Rounded2558‖ ≤
          batchC02702PlusMidpointP026Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP026Factor2558
      batchC02702PlusMidpointP026Center2558)
  rw [batchC02702PlusMidpointP026RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP026Factor2558 * embedPair2542
        batchC02702PlusMidpointP026Center2558)
    (embedPair2542 batchC02702PlusMidpointP026Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP026DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP026Factor2558,
      batchC02702PlusMidpointP026Error2558, rounding2542,
      batchC02702PlusMidpointP026Radius2558]

theorem batchC02702PlusMidpointP026DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP026Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP026RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP026Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP026Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP026Rounded2558]

def batchC02702PlusMidpointP027Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP027Radius2558 : ℝ := ((2199062523981 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702PlusMidpointP027RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP027Factor2558
        batchC02702PlusMidpointP027Center2558) =
        batchC02702PlusMidpointP027Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP027RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP027Rounded2558‖ ≤
          batchC02702PlusMidpointP027Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP027Factor2558
      batchC02702PlusMidpointP027Center2558)
  rw [batchC02702PlusMidpointP027RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP027Factor2558 * embedPair2542
        batchC02702PlusMidpointP027Center2558)
    (embedPair2542 batchC02702PlusMidpointP027Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP027DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP027Factor2558,
      batchC02702PlusMidpointP027Error2558, rounding2542,
      batchC02702PlusMidpointP027Radius2558]

theorem batchC02702PlusMidpointP027DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP027Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP027RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP027Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP027Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP027Rounded2558]

def batchC02702PlusMidpointP028Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP028Radius2558 : ℝ := ((1099531262003 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02702PlusMidpointP028RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP028Factor2558
        batchC02702PlusMidpointP028Center2558) =
        batchC02702PlusMidpointP028Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP028RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP028Rounded2558‖ ≤
          batchC02702PlusMidpointP028Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP028Factor2558
      batchC02702PlusMidpointP028Center2558)
  rw [batchC02702PlusMidpointP028RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP028Factor2558 * embedPair2542
        batchC02702PlusMidpointP028Center2558)
    (embedPair2542 batchC02702PlusMidpointP028Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP028DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP028Factor2558,
      batchC02702PlusMidpointP028Error2558, rounding2542,
      batchC02702PlusMidpointP028Radius2558]

theorem batchC02702PlusMidpointP028DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP028Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP028RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP028Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP028Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP028Rounded2558]

def batchC02702PlusMidpointP029Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP029Radius2558 : ℝ := ((549765631011 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02702PlusMidpointP029RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702PlusMidpointP029Factor2558
        batchC02702PlusMidpointP029Center2558) =
        batchC02702PlusMidpointP029Rounded2558 := by
  cbv

theorem batchC02702PlusMidpointP029RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP029Rounded2558‖ ≤
          batchC02702PlusMidpointP029Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702PlusMidpointP029Factor2558
      batchC02702PlusMidpointP029Center2558)
  rw [batchC02702PlusMidpointP029RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP029Factor2558 * embedPair2542
        batchC02702PlusMidpointP029Center2558)
    (embedPair2542 batchC02702PlusMidpointP029Rounded2558)).trans (add_le_add
        batchC02702PlusMidpointP029DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702PlusMidpointP029Factor2558,
      batchC02702PlusMidpointP029Error2558, rounding2542,
      batchC02702PlusMidpointP029Radius2558]

theorem batchC02702PlusMidpointP029DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02702PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02702PlusMidpointPosition2558)
    (embedPair2542 batchC02702PlusMidpointP029Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702PlusMidpointP029RoundedError2558
      (embedPair_magnitude2542
      batchC02702PlusMidpointP029Rounded2558))
  apply h'.trans
  norm_num [batchC02702PlusMidpointP029Radius2558, pairMagnitude2542,
      batchC02702PlusMidpointP029Rounded2558]

noncomputable def batchC02702PlusSignedMidpointValue2558 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchC02702PlusMidpointP000Rounded2558
  | 1 => embedPair2542 batchC02702PlusMidpointP001Rounded2558
  | 2 => embedPair2542 batchC02702PlusMidpointP002Rounded2558
  | 3 => embedPair2542 batchC02702PlusMidpointP003Rounded2558
  | 4 => embedPair2542 batchC02702PlusMidpointP004Rounded2558
  | 5 => embedPair2542 batchC02702PlusMidpointP005Rounded2558
  | 6 => embedPair2542 batchC02702PlusMidpointP006Rounded2558
  | 7 => embedPair2542 batchC02702PlusMidpointP007Rounded2558
  | 8 => embedPair2542 batchC02702PlusMidpointP008Rounded2558
  | 9 => embedPair2542 batchC02702PlusMidpointP009Rounded2558
  | 10 => embedPair2542 batchC02702PlusMidpointP010Rounded2558
  | 11 => embedPair2542 batchC02702PlusMidpointP011Rounded2558
  | 12 => embedPair2542 batchC02702PlusMidpointP012Rounded2558
  | 13 => embedPair2542 batchC02702PlusMidpointP013Rounded2558
  | 14 => embedPair2542 batchC02702PlusMidpointP014Rounded2558
  | 15 => embedPair2542 batchC02702PlusMidpointP015Rounded2558
  | 16 => embedPair2542 batchC02702PlusMidpointP016Rounded2558
  | 17 => embedPair2542 batchC02702PlusMidpointP017Rounded2558
  | 18 => embedPair2542 batchC02702PlusMidpointP018Rounded2558
  | 19 => embedPair2542 batchC02702PlusMidpointP019Rounded2558
  | 20 => embedPair2542 batchC02702PlusMidpointP020Rounded2558
  | 21 => embedPair2542 batchC02702PlusMidpointP021Rounded2558
  | 22 => embedPair2542 batchC02702PlusMidpointP022Rounded2558
  | 23 => embedPair2542 batchC02702PlusMidpointP023Rounded2558
  | 24 => embedPair2542 batchC02702PlusMidpointP024Rounded2558
  | 25 => embedPair2542 batchC02702PlusMidpointP025Rounded2558
  | 26 => embedPair2542 batchC02702PlusMidpointP026Rounded2558
  | 27 => embedPair2542 batchC02702PlusMidpointP027Rounded2558
  | 28 => embedPair2542 batchC02702PlusMidpointP028Rounded2558
  | 29 => embedPair2542 batchC02702PlusMidpointP029Rounded2558
  | _ => 0

noncomputable def batchC02702PlusSignedMidpointError2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02702PlusMidpointP000Radius2558
  | 1 => batchC02702PlusMidpointP001Radius2558
  | 2 => batchC02702PlusMidpointP002Radius2558
  | 3 => batchC02702PlusMidpointP003Radius2558
  | 4 => batchC02702PlusMidpointP004Radius2558
  | 5 => batchC02702PlusMidpointP005Radius2558
  | 6 => batchC02702PlusMidpointP006Radius2558
  | 7 => batchC02702PlusMidpointP007Radius2558
  | 8 => batchC02702PlusMidpointP008Radius2558
  | 9 => batchC02702PlusMidpointP009Radius2558
  | 10 => batchC02702PlusMidpointP010Radius2558
  | 11 => batchC02702PlusMidpointP011Radius2558
  | 12 => batchC02702PlusMidpointP012Radius2558
  | 13 => batchC02702PlusMidpointP013Radius2558
  | 14 => batchC02702PlusMidpointP014Radius2558
  | 15 => batchC02702PlusMidpointP015Radius2558
  | 16 => batchC02702PlusMidpointP016Radius2558
  | 17 => batchC02702PlusMidpointP017Radius2558
  | 18 => batchC02702PlusMidpointP018Radius2558
  | 19 => batchC02702PlusMidpointP019Radius2558
  | 20 => batchC02702PlusMidpointP020Radius2558
  | 21 => batchC02702PlusMidpointP021Radius2558
  | 22 => batchC02702PlusMidpointP022Radius2558
  | 23 => batchC02702PlusMidpointP023Radius2558
  | 24 => batchC02702PlusMidpointP024Radius2558
  | 25 => batchC02702PlusMidpointP025Radius2558
  | 26 => batchC02702PlusMidpointP026Radius2558
  | 27 => batchC02702PlusMidpointP027Radius2558
  | 28 => batchC02702PlusMidpointP028Radius2558
  | 29 => batchC02702PlusMidpointP029Radius2558
  | _ => 0

theorem batchC02702PlusSignedMidpointExpError2558 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02702PlusMidpointPosition2558 -
        batchC02702PlusSignedMidpointValue2558 i‖ ≤ batchC02702PlusSignedMidpointError2558 i := by
  fin_cases i
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP000RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP001RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP002RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP003RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP004RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP005RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP006RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP007RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP008RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP009RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP010RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP011RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP012RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP013RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP014RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP015RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP016RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP017RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP018RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP019RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP020RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP021RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP022RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP023RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP024RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP025RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP026RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP027RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP028RoundedError2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP029RoundedError2558

theorem batchC02702PlusSignedMidpointUnitNorm2558 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02702PlusMidpointPosition2558‖ ≤ 1 :=
        by
  fin_cases i
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP000DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP001DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP002DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP003DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP004DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP005DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP006DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP007DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP008DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP009DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP010DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP011DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP012DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP013DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP014DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP015DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP016DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP017DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP018DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP019DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP020DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP021DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP022DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP023DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP024DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP025DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP026DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP027DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP028DerivativeNorm2558
  · simpa only [batchC02702PlusSignedMidpointValue2558, batchC02702PlusSignedMidpointError2558]
      using
      batchC02702PlusMidpointP029DerivativeNorm2558

noncomputable def batchC02702PlusSignedMidpointSum2558 : ℂ := ⟨(((-(((1884 * 10^40
        + 1855147832596646579038251721002774201767) * 10^40
        + 1155679735648916142343509937758255746664) * 10^40
        + 6512517382881707756618142877113117697605)) : ℝ) /
        (((10830740 * 10^40
        + 9926594330452281804068089207165485823256) * 10^40
        + 8678349675968586177586448361572508999990) * 10^40
        + 23844295226942934417817982702456930304)),
    (((-(((512 * 10^40
        + 8390866105245351106173541910286956378285) * 10^40
        + 8404017909853304949325754688811957197105) * 10^40
        + 2168475433850278434913310364090092384379)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216))⟩

noncomputable def batchC02702PlusSignedMidpointUpper2558 : ℝ := ((17447 : ℝ) /
        100000000)

theorem batchC02702PlusSignedMidpointSum_eq2558 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02702PlusSignedMidpointValue2558 i) =
      batchC02702PlusSignedMidpointSum2558 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
        batchC02702PlusSignedMidpointValue2558,
      batchC02702PlusSignedMidpointSum2558, embedPair2542, batchC02702PlusMidpointP000Rounded2558,
      batchC02702PlusMidpointP001Rounded2558,
      batchC02702PlusMidpointP002Rounded2558,
      batchC02702PlusMidpointP003Rounded2558,
      batchC02702PlusMidpointP004Rounded2558,
      batchC02702PlusMidpointP005Rounded2558,
      batchC02702PlusMidpointP006Rounded2558,
      batchC02702PlusMidpointP007Rounded2558,
      batchC02702PlusMidpointP008Rounded2558,
      batchC02702PlusMidpointP009Rounded2558,
      batchC02702PlusMidpointP010Rounded2558,
      batchC02702PlusMidpointP011Rounded2558,
      batchC02702PlusMidpointP012Rounded2558,
      batchC02702PlusMidpointP013Rounded2558,
      batchC02702PlusMidpointP014Rounded2558,
      batchC02702PlusMidpointP015Rounded2558,
      batchC02702PlusMidpointP016Rounded2558,
      batchC02702PlusMidpointP017Rounded2558,
      batchC02702PlusMidpointP018Rounded2558,
      batchC02702PlusMidpointP019Rounded2558,
      batchC02702PlusMidpointP020Rounded2558,
      batchC02702PlusMidpointP021Rounded2558,
      batchC02702PlusMidpointP022Rounded2558,
      batchC02702PlusMidpointP023Rounded2558,
      batchC02702PlusMidpointP024Rounded2558,
      batchC02702PlusMidpointP025Rounded2558,
      batchC02702PlusMidpointP026Rounded2558,
      batchC02702PlusMidpointP027Rounded2558,
      batchC02702PlusMidpointP028Rounded2558,
      batchC02702PlusMidpointP029Rounded2558, Complex.mul_re, Complex.mul_im]

theorem batchC02702PlusSignedMidpointSum_norm2558 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02702PlusSignedMidpointValue2558 i‖ ≤
        ((17437 : ℝ) /
        100000000) := by
  rw [batchC02702PlusSignedMidpointSum_eq2558]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchC02702PlusSignedMidpointSum2558]

theorem batchC02702PlusSignedMidpointCharge2558 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchC02702PlusSignedMidpointError2558 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
      batchC02702PlusSignedMidpointError2558,
      batchC02702PlusMidpointP000Radius2558,
      batchC02702PlusMidpointP001Radius2558,
      batchC02702PlusMidpointP002Radius2558,
      batchC02702PlusMidpointP003Radius2558,
      batchC02702PlusMidpointP004Radius2558,
      batchC02702PlusMidpointP005Radius2558,
      batchC02702PlusMidpointP006Radius2558,
      batchC02702PlusMidpointP007Radius2558,
      batchC02702PlusMidpointP008Radius2558,
      batchC02702PlusMidpointP009Radius2558,
      batchC02702PlusMidpointP010Radius2558,
      batchC02702PlusMidpointP011Radius2558,
      batchC02702PlusMidpointP012Radius2558,
      batchC02702PlusMidpointP013Radius2558,
      batchC02702PlusMidpointP014Radius2558,
      batchC02702PlusMidpointP015Radius2558,
      batchC02702PlusMidpointP016Radius2558,
      batchC02702PlusMidpointP017Radius2558,
      batchC02702PlusMidpointP018Radius2558,
      batchC02702PlusMidpointP019Radius2558,
      batchC02702PlusMidpointP020Radius2558,
      batchC02702PlusMidpointP021Radius2558,
      batchC02702PlusMidpointP022Radius2558,
      batchC02702PlusMidpointP023Radius2558,
      batchC02702PlusMidpointP024Radius2558,
      batchC02702PlusMidpointP025Radius2558,
      batchC02702PlusMidpointP026Radius2558,
      batchC02702PlusMidpointP027Radius2558,
      batchC02702PlusMidpointP028Radius2558,
      batchC02702PlusMidpointP029Radius2558]

theorem batchC02702PlusSignedMidpointUpper_le2558 :
    signedJetUpper2539 2 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchC02702PlusMidpointPosition2558 ≤
          batchC02702PlusSignedMidpointUpper2558 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02702PlusMidpointPosition2558‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02702PlusSignedMidpointValue2558 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchC02702PlusSignedMidpointError2558 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (batchC02702PlusSignedMidpointExpError2558 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02702PlusMidpointPosition2558‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchC02702PlusSignedMidpointUnitNorm2558 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02702PlusMidpointPosition2558‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchC02702PlusSignedMidpointUpper2558
  linarith [batchC02702PlusSignedMidpointSum_norm2558, batchC02702PlusSignedMidpointCharge2558]

theorem batchC02702PlusPhysicalSecond2558 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        batchC02702PlusMidpointPosition2558‖ ≤
      batchC02702PlusSignedMidpointUpper2558 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchC02702PlusMidpointPosition2558
  exact h.trans batchC02702PlusSignedMidpointUpper_le2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02702PlusSignedMidpointExpError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusSignedMidpointSum_eq2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusSignedMidpointCharge2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusSignedMidpointUpper_le2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusPhysicalSecond2558
