import ConnesWeilRH.Dev.C1RouteABatchC02700PlusMidpoint2558

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem batchC02700PlusMidpoint_triangle2558 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def batchC02700PlusMidpointP000Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP000Radius2558 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02700PlusMidpointP000RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP000Factor2558
        batchC02700PlusMidpointP000Center2558) =
        batchC02700PlusMidpointP000Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP000RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP000Rounded2558‖ ≤
          batchC02700PlusMidpointP000Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP000Factor2558
      batchC02700PlusMidpointP000Center2558)
  rw [batchC02700PlusMidpointP000RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP000Factor2558 * embedPair2542
        batchC02700PlusMidpointP000Center2558)
    (embedPair2542 batchC02700PlusMidpointP000Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP000DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP000Factor2558,
      batchC02700PlusMidpointP000Error2558, rounding2542,
      batchC02700PlusMidpointP000Radius2558]

theorem batchC02700PlusMidpointP000DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP000Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP000RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP000Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP000Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP000Rounded2558]

def batchC02700PlusMidpointP001Rounded2558 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP001Radius2558 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700PlusMidpointP001RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP001Factor2558
        batchC02700PlusMidpointP001Center2558) =
        batchC02700PlusMidpointP001Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP001RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP001Rounded2558‖ ≤
          batchC02700PlusMidpointP001Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP001Factor2558
      batchC02700PlusMidpointP001Center2558)
  rw [batchC02700PlusMidpointP001RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP001Factor2558 * embedPair2542
        batchC02700PlusMidpointP001Center2558)
    (embedPair2542 batchC02700PlusMidpointP001Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP001DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP001Factor2558,
      batchC02700PlusMidpointP001Error2558, rounding2542,
      batchC02700PlusMidpointP001Radius2558]

theorem batchC02700PlusMidpointP001DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP001Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP001RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP001Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP001Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP001Rounded2558]

def batchC02700PlusMidpointP002Rounded2558 : RatPair2542 :=
  (((1339907 : ℚ) /
        1267650600228229401496703205376),
    (((-524869) : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC02700PlusMidpointP002Radius2558 : ℝ := ((2199023262191 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700PlusMidpointP002RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP002Factor2558
        batchC02700PlusMidpointP002Center2558) =
        batchC02700PlusMidpointP002Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP002RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP002Rounded2558‖ ≤
          batchC02700PlusMidpointP002Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP002Factor2558
      batchC02700PlusMidpointP002Center2558)
  rw [batchC02700PlusMidpointP002RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP002Factor2558 * embedPair2542
        batchC02700PlusMidpointP002Center2558)
    (embedPair2542 batchC02700PlusMidpointP002Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP002DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP002Factor2558,
      batchC02700PlusMidpointP002Error2558, rounding2542,
      batchC02700PlusMidpointP002Radius2558]

theorem batchC02700PlusMidpointP002DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP002Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP002RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP002Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP002Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP002Rounded2558]

def batchC02700PlusMidpointP003Rounded2558 : RatPair2542 :=
  (((15448181489715 : ℚ) /
        1267650600228229401496703205376),
    ((3802480427995 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02700PlusMidpointP003Radius2558 : ℝ := ((569261515263 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02700PlusMidpointP003RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP003Factor2558
        batchC02700PlusMidpointP003Center2558) =
        batchC02700PlusMidpointP003Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP003RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP003Rounded2558‖ ≤
          batchC02700PlusMidpointP003Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP003Factor2558
      batchC02700PlusMidpointP003Center2558)
  rw [batchC02700PlusMidpointP003RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP003Factor2558 * embedPair2542
        batchC02700PlusMidpointP003Center2558)
    (embedPair2542 batchC02700PlusMidpointP003Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP003DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP003Factor2558,
      batchC02700PlusMidpointP003Error2558, rounding2542,
      batchC02700PlusMidpointP003Radius2558]

theorem batchC02700PlusMidpointP003DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP003Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP003RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP003Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP003Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP003Rounded2558]

def batchC02700PlusMidpointP004Rounded2558 : RatPair2542 :=
  (((762028936138355 : ℚ) /
        158456325028528675187087900672),
    (((-1970922237903599) : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC02700PlusMidpointP004Radius2558 : ℝ := ((17135354181433 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02700PlusMidpointP004RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP004Factor2558
        batchC02700PlusMidpointP004Center2558) =
        batchC02700PlusMidpointP004Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP004RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP004Rounded2558‖ ≤
          batchC02700PlusMidpointP004Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP004Factor2558
      batchC02700PlusMidpointP004Center2558)
  rw [batchC02700PlusMidpointP004RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP004Factor2558 * embedPair2542
        batchC02700PlusMidpointP004Center2558)
    (embedPair2542 batchC02700PlusMidpointP004Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP004DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP004Factor2558,
      batchC02700PlusMidpointP004Error2558, rounding2542,
      batchC02700PlusMidpointP004Radius2558]

theorem batchC02700PlusMidpointP004DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP004Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP004RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP004Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP004Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP004Rounded2558]

def batchC02700PlusMidpointP005Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP005Radius2558 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02700PlusMidpointP005RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP005Factor2558
        batchC02700PlusMidpointP005Center2558) =
        batchC02700PlusMidpointP005Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP005RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP005Rounded2558‖ ≤
          batchC02700PlusMidpointP005Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP005Factor2558
      batchC02700PlusMidpointP005Center2558)
  rw [batchC02700PlusMidpointP005RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP005Factor2558 * embedPair2542
        batchC02700PlusMidpointP005Center2558)
    (embedPair2542 batchC02700PlusMidpointP005Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP005DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP005Factor2558,
      batchC02700PlusMidpointP005Error2558, rounding2542,
      batchC02700PlusMidpointP005Radius2558]

theorem batchC02700PlusMidpointP005DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP005Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP005RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP005Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP005Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP005Rounded2558]

def batchC02700PlusMidpointP006Rounded2558 : RatPair2542 :=
  (((1 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP006Radius2558 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700PlusMidpointP006RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP006Factor2558
        batchC02700PlusMidpointP006Center2558) =
        batchC02700PlusMidpointP006Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP006RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP006Rounded2558‖ ≤
          batchC02700PlusMidpointP006Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP006Factor2558
      batchC02700PlusMidpointP006Center2558)
  rw [batchC02700PlusMidpointP006RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP006Factor2558 * embedPair2542
        batchC02700PlusMidpointP006Center2558)
    (embedPair2542 batchC02700PlusMidpointP006Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP006DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP006Factor2558,
      batchC02700PlusMidpointP006Error2558, rounding2542,
      batchC02700PlusMidpointP006Radius2558]

theorem batchC02700PlusMidpointP006DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP006Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP006RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP006Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP006Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP006Rounded2558]

def batchC02700PlusMidpointP007Rounded2558 : RatPair2542 :=
  (((1852709455279 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP007Radius2558 : ℝ := ((1099646212197 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02700PlusMidpointP007RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP007Factor2558
        batchC02700PlusMidpointP007Center2558) =
        batchC02700PlusMidpointP007Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP007RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP007Rounded2558‖ ≤
          batchC02700PlusMidpointP007Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP007Factor2558
      batchC02700PlusMidpointP007Center2558)
  rw [batchC02700PlusMidpointP007RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP007Factor2558 * embedPair2542
        batchC02700PlusMidpointP007Center2558)
    (embedPair2542 batchC02700PlusMidpointP007Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP007DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP007Factor2558,
      batchC02700PlusMidpointP007Error2558, rounding2542,
      batchC02700PlusMidpointP007Radius2558]

theorem batchC02700PlusMidpointP007DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP007Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP007RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP007Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP007Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP007Rounded2558]

def batchC02700PlusMidpointP008Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP008Radius2558 : ℝ := ((2223573724293 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700PlusMidpointP008RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP008Factor2558
        batchC02700PlusMidpointP008Center2558) =
        batchC02700PlusMidpointP008Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP008RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP008Rounded2558‖ ≤
          batchC02700PlusMidpointP008Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP008Factor2558
      batchC02700PlusMidpointP008Center2558)
  rw [batchC02700PlusMidpointP008RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP008Factor2558 * embedPair2542
        batchC02700PlusMidpointP008Center2558)
    (embedPair2542 batchC02700PlusMidpointP008Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP008DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP008Factor2558,
      batchC02700PlusMidpointP008Error2558, rounding2542,
      batchC02700PlusMidpointP008Radius2558]

theorem batchC02700PlusMidpointP008DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP008Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP008RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP008Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP008Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP008Rounded2558]

def batchC02700PlusMidpointP009Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP009Radius2558 : ℝ := ((1111786863637 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02700PlusMidpointP009RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP009Factor2558
        batchC02700PlusMidpointP009Center2558) =
        batchC02700PlusMidpointP009Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP009RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP009Rounded2558‖ ≤
          batchC02700PlusMidpointP009Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP009Factor2558
      batchC02700PlusMidpointP009Center2558)
  rw [batchC02700PlusMidpointP009RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP009Factor2558 * embedPair2542
        batchC02700PlusMidpointP009Center2558)
    (embedPair2542 batchC02700PlusMidpointP009Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP009DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP009Factor2558,
      batchC02700PlusMidpointP009Error2558, rounding2542,
      batchC02700PlusMidpointP009Radius2558]

theorem batchC02700PlusMidpointP009DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP009Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP009RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP009Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP009Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP009Rounded2558]

def batchC02700PlusMidpointP010Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP010Radius2558 : ℝ := ((2223573729001 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700PlusMidpointP010RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP010Factor2558
        batchC02700PlusMidpointP010Center2558) =
        batchC02700PlusMidpointP010Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP010RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP010Rounded2558‖ ≤
          batchC02700PlusMidpointP010Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP010Factor2558
      batchC02700PlusMidpointP010Center2558)
  rw [batchC02700PlusMidpointP010RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP010Factor2558 * embedPair2542
        batchC02700PlusMidpointP010Center2558)
    (embedPair2542 batchC02700PlusMidpointP010Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP010DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP010Factor2558,
      batchC02700PlusMidpointP010Error2558, rounding2542,
      batchC02700PlusMidpointP010Radius2558]

theorem batchC02700PlusMidpointP010DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP010Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP010RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP010Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP010Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP010Rounded2558]

def batchC02700PlusMidpointP011Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP011Radius2558 : ℝ := ((277946716269 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02700PlusMidpointP011RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP011Factor2558
        batchC02700PlusMidpointP011Center2558) =
        batchC02700PlusMidpointP011Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP011RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP011Rounded2558‖ ≤
          batchC02700PlusMidpointP011Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP011Factor2558
      batchC02700PlusMidpointP011Center2558)
  rw [batchC02700PlusMidpointP011RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP011Factor2558 * embedPair2542
        batchC02700PlusMidpointP011Center2558)
    (embedPair2542 batchC02700PlusMidpointP011Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP011DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP011Factor2558,
      batchC02700PlusMidpointP011Error2558, rounding2542,
      batchC02700PlusMidpointP011Radius2558]

theorem batchC02700PlusMidpointP011DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP011Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP011RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP011Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP011Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP011Rounded2558]

def batchC02700PlusMidpointP012Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP012Radius2558 : ℝ := ((138973358209 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem batchC02700PlusMidpointP012RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP012Factor2558
        batchC02700PlusMidpointP012Center2558) =
        batchC02700PlusMidpointP012Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP012RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP012Rounded2558‖ ≤
          batchC02700PlusMidpointP012Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP012Factor2558
      batchC02700PlusMidpointP012Center2558)
  rw [batchC02700PlusMidpointP012RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP012Factor2558 * embedPair2542
        batchC02700PlusMidpointP012Center2558)
    (embedPair2542 batchC02700PlusMidpointP012Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP012DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP012Factor2558,
      batchC02700PlusMidpointP012Error2558, rounding2542,
      batchC02700PlusMidpointP012Radius2558]

theorem batchC02700PlusMidpointP012DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP012Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP012RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP012Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP012Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP012Rounded2558]

def batchC02700PlusMidpointP013Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP013Radius2558 : ℝ := ((1111786866215 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02700PlusMidpointP013RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP013Factor2558
        batchC02700PlusMidpointP013Center2558) =
        batchC02700PlusMidpointP013Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP013RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP013Rounded2558‖ ≤
          batchC02700PlusMidpointP013Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP013Factor2558
      batchC02700PlusMidpointP013Center2558)
  rw [batchC02700PlusMidpointP013RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP013Factor2558 * embedPair2542
        batchC02700PlusMidpointP013Center2558)
    (embedPair2542 batchC02700PlusMidpointP013Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP013DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP013Factor2558,
      batchC02700PlusMidpointP013Error2558, rounding2542,
      batchC02700PlusMidpointP013Radius2558]

theorem batchC02700PlusMidpointP013DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP013Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP013RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP013Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP013Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP013Rounded2558]

def batchC02700PlusMidpointP014Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP014Radius2558 : ℝ := ((2223573734443 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700PlusMidpointP014RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP014Factor2558
        batchC02700PlusMidpointP014Center2558) =
        batchC02700PlusMidpointP014Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP014RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP014Rounded2558‖ ≤
          batchC02700PlusMidpointP014Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP014Factor2558
      batchC02700PlusMidpointP014Center2558)
  rw [batchC02700PlusMidpointP014RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP014Factor2558 * embedPair2542
        batchC02700PlusMidpointP014Center2558)
    (embedPair2542 batchC02700PlusMidpointP014Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP014DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP014Factor2558,
      batchC02700PlusMidpointP014Error2558, rounding2542,
      batchC02700PlusMidpointP014Radius2558]

theorem batchC02700PlusMidpointP014DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP014Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP014RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP014Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP014Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP014Rounded2558]

def batchC02700PlusMidpointP015Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP015Radius2558 : ℝ := ((2223573735885 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700PlusMidpointP015RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP015Factor2558
        batchC02700PlusMidpointP015Center2558) =
        batchC02700PlusMidpointP015Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP015RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP015Rounded2558‖ ≤
          batchC02700PlusMidpointP015Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP015Factor2558
      batchC02700PlusMidpointP015Center2558)
  rw [batchC02700PlusMidpointP015RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP015Factor2558 * embedPair2542
        batchC02700PlusMidpointP015Center2558)
    (embedPair2542 batchC02700PlusMidpointP015Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP015DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP015Factor2558,
      batchC02700PlusMidpointP015Error2558, rounding2542,
      batchC02700PlusMidpointP015Radius2558]

theorem batchC02700PlusMidpointP015DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP015Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP015RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP015Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP015Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP015Rounded2558]

def batchC02700PlusMidpointP016Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP016Radius2558 : ℝ := ((69486679279 : ℝ) /
        (4 * 10^40
        + 3556142965880123323311949751266331066368))

theorem batchC02700PlusMidpointP016RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP016Factor2558
        batchC02700PlusMidpointP016Center2558) =
        batchC02700PlusMidpointP016Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP016RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP016Rounded2558‖ ≤
          batchC02700PlusMidpointP016Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP016Factor2558
      batchC02700PlusMidpointP016Center2558)
  rw [batchC02700PlusMidpointP016RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP016Factor2558 * embedPair2542
        batchC02700PlusMidpointP016Center2558)
    (embedPair2542 batchC02700PlusMidpointP016Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP016DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP016Factor2558,
      batchC02700PlusMidpointP016Error2558, rounding2542,
      batchC02700PlusMidpointP016Radius2558]

theorem batchC02700PlusMidpointP016DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP016Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP016RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP016Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP016Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP016Rounded2558]

def batchC02700PlusMidpointP017Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP017Radius2558 : ℝ := ((277946717369 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02700PlusMidpointP017RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP017Factor2558
        batchC02700PlusMidpointP017Center2558) =
        batchC02700PlusMidpointP017Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP017RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP017Rounded2558‖ ≤
          batchC02700PlusMidpointP017Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP017Factor2558
      batchC02700PlusMidpointP017Center2558)
  rw [batchC02700PlusMidpointP017RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP017Factor2558 * embedPair2542
        batchC02700PlusMidpointP017Center2558)
    (embedPair2542 batchC02700PlusMidpointP017Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP017DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP017Factor2558,
      batchC02700PlusMidpointP017Error2558, rounding2542,
      batchC02700PlusMidpointP017Radius2558]

theorem batchC02700PlusMidpointP017DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP017Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP017RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP017Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP017Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP017Rounded2558]

def batchC02700PlusMidpointP018Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP018Radius2558 : ℝ := ((1111786869859 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02700PlusMidpointP018RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP018Factor2558
        batchC02700PlusMidpointP018Center2558) =
        batchC02700PlusMidpointP018Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP018RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP018Rounded2558‖ ≤
          batchC02700PlusMidpointP018Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP018Factor2558
      batchC02700PlusMidpointP018Center2558)
  rw [batchC02700PlusMidpointP018RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP018Factor2558 * embedPair2542
        batchC02700PlusMidpointP018Center2558)
    (embedPair2542 batchC02700PlusMidpointP018Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP018DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP018Factor2558,
      batchC02700PlusMidpointP018Error2558, rounding2542,
      batchC02700PlusMidpointP018Radius2558]

theorem batchC02700PlusMidpointP018DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP018Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP018RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP018Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP018Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP018Rounded2558]

def batchC02700PlusMidpointP019Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP019Radius2558 : ℝ := ((2223573741101 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700PlusMidpointP019RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP019Factor2558
        batchC02700PlusMidpointP019Center2558) =
        batchC02700PlusMidpointP019Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP019RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP019Rounded2558‖ ≤
          batchC02700PlusMidpointP019Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP019Factor2558
      batchC02700PlusMidpointP019Center2558)
  rw [batchC02700PlusMidpointP019RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP019Factor2558 * embedPair2542
        batchC02700PlusMidpointP019Center2558)
    (embedPair2542 batchC02700PlusMidpointP019Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP019DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP019Factor2558,
      batchC02700PlusMidpointP019Error2558, rounding2542,
      batchC02700PlusMidpointP019Radius2558]

theorem batchC02700PlusMidpointP019DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP019Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP019RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP019Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP019Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP019Rounded2558]

def batchC02700PlusMidpointP020Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP020Radius2558 : ℝ := ((1111786871303 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02700PlusMidpointP020RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP020Factor2558
        batchC02700PlusMidpointP020Center2558) =
        batchC02700PlusMidpointP020Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP020RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP020Rounded2558‖ ≤
          batchC02700PlusMidpointP020Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP020Factor2558
      batchC02700PlusMidpointP020Center2558)
  rw [batchC02700PlusMidpointP020RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP020Factor2558 * embedPair2542
        batchC02700PlusMidpointP020Center2558)
    (embedPair2542 batchC02700PlusMidpointP020Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP020DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP020Factor2558,
      batchC02700PlusMidpointP020Error2558, rounding2542,
      batchC02700PlusMidpointP020Radius2558]

theorem batchC02700PlusMidpointP020DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP020Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP020RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP020Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP020Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP020Rounded2558]

def batchC02700PlusMidpointP021Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP021Radius2558 : ℝ := ((2223573743861 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700PlusMidpointP021RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP021Factor2558
        batchC02700PlusMidpointP021Center2558) =
        batchC02700PlusMidpointP021Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP021RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP021Rounded2558‖ ≤
          batchC02700PlusMidpointP021Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP021Factor2558
      batchC02700PlusMidpointP021Center2558)
  rw [batchC02700PlusMidpointP021RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP021Factor2558 * embedPair2542
        batchC02700PlusMidpointP021Center2558)
    (embedPair2542 batchC02700PlusMidpointP021Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP021DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP021Factor2558,
      batchC02700PlusMidpointP021Error2558, rounding2542,
      batchC02700PlusMidpointP021Radius2558]

theorem batchC02700PlusMidpointP021DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP021Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP021RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP021Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP021Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP021Rounded2558]

def batchC02700PlusMidpointP022Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP022Radius2558 : ℝ := ((277946718063 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02700PlusMidpointP022RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP022Factor2558
        batchC02700PlusMidpointP022Center2558) =
        batchC02700PlusMidpointP022Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP022RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP022Rounded2558‖ ≤
          batchC02700PlusMidpointP022Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP022Factor2558
      batchC02700PlusMidpointP022Center2558)
  rw [batchC02700PlusMidpointP022RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP022Factor2558 * embedPair2542
        batchC02700PlusMidpointP022Center2558)
    (embedPair2542 batchC02700PlusMidpointP022Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP022DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP022Factor2558,
      batchC02700PlusMidpointP022Error2558, rounding2542,
      batchC02700PlusMidpointP022Radius2558]

theorem batchC02700PlusMidpointP022DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP022Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP022RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP022Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP022Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP022Rounded2558]

def batchC02700PlusMidpointP023Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP023Radius2558 : ℝ := ((555893436589 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02700PlusMidpointP023RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP023Factor2558
        batchC02700PlusMidpointP023Center2558) =
        batchC02700PlusMidpointP023Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP023RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP023Rounded2558‖ ≤
          batchC02700PlusMidpointP023Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP023Factor2558
      batchC02700PlusMidpointP023Center2558)
  rw [batchC02700PlusMidpointP023RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP023Factor2558 * embedPair2542
        batchC02700PlusMidpointP023Center2558)
    (embedPair2542 batchC02700PlusMidpointP023Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP023DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP023Factor2558,
      batchC02700PlusMidpointP023Error2558, rounding2542,
      batchC02700PlusMidpointP023Radius2558]

theorem batchC02700PlusMidpointP023DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP023Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP023RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP023Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP023Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP023Rounded2558]

def batchC02700PlusMidpointP024Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP024Radius2558 : ℝ := ((277946718401 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02700PlusMidpointP024RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP024Factor2558
        batchC02700PlusMidpointP024Center2558) =
        batchC02700PlusMidpointP024Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP024RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP024Rounded2558‖ ≤
          batchC02700PlusMidpointP024Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP024Factor2558
      batchC02700PlusMidpointP024Center2558)
  rw [batchC02700PlusMidpointP024RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP024Factor2558 * embedPair2542
        batchC02700PlusMidpointP024Center2558)
    (embedPair2542 batchC02700PlusMidpointP024Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP024DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP024Factor2558,
      batchC02700PlusMidpointP024Error2558, rounding2542,
      batchC02700PlusMidpointP024Radius2558]

theorem batchC02700PlusMidpointP024DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP024Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP024RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP024Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP024Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP024Rounded2558]

def batchC02700PlusMidpointP025Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP025Radius2558 : ℝ := ((2223573748275 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700PlusMidpointP025RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP025Factor2558
        batchC02700PlusMidpointP025Center2558) =
        batchC02700PlusMidpointP025Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP025RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP025Rounded2558‖ ≤
          batchC02700PlusMidpointP025Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP025Factor2558
      batchC02700PlusMidpointP025Center2558)
  rw [batchC02700PlusMidpointP025RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP025Factor2558 * embedPair2542
        batchC02700PlusMidpointP025Center2558)
    (embedPair2542 batchC02700PlusMidpointP025Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP025DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP025Factor2558,
      batchC02700PlusMidpointP025Error2558, rounding2542,
      batchC02700PlusMidpointP025Radius2558]

theorem batchC02700PlusMidpointP025DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP025Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP025RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP025Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP025Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP025Rounded2558]

def batchC02700PlusMidpointP026Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP026Radius2558 : ℝ := ((1111786874683 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02700PlusMidpointP026RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP026Factor2558
        batchC02700PlusMidpointP026Center2558) =
        batchC02700PlusMidpointP026Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP026RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP026Rounded2558‖ ≤
          batchC02700PlusMidpointP026Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP026Factor2558
      batchC02700PlusMidpointP026Center2558)
  rw [batchC02700PlusMidpointP026RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP026Factor2558 * embedPair2542
        batchC02700PlusMidpointP026Center2558)
    (embedPair2542 batchC02700PlusMidpointP026Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP026DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP026Factor2558,
      batchC02700PlusMidpointP026Error2558, rounding2542,
      batchC02700PlusMidpointP026Radius2558]

theorem batchC02700PlusMidpointP026DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP026Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP026RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP026Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP026Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP026Rounded2558]

def batchC02700PlusMidpointP027Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP027Radius2558 : ℝ := ((555893437735 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02700PlusMidpointP027RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP027Factor2558
        batchC02700PlusMidpointP027Center2558) =
        batchC02700PlusMidpointP027Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP027RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP027Rounded2558‖ ≤
          batchC02700PlusMidpointP027Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP027Factor2558
      batchC02700PlusMidpointP027Center2558)
  rw [batchC02700PlusMidpointP027RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP027Factor2558 * embedPair2542
        batchC02700PlusMidpointP027Center2558)
    (embedPair2542 batchC02700PlusMidpointP027Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP027DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP027Factor2558,
      batchC02700PlusMidpointP027Error2558, rounding2542,
      batchC02700PlusMidpointP027Radius2558]

theorem batchC02700PlusMidpointP027DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP027Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP027RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP027Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP027Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP027Rounded2558]

def batchC02700PlusMidpointP028Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP028Radius2558 : ℝ := ((555893437891 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02700PlusMidpointP028RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP028Factor2558
        batchC02700PlusMidpointP028Center2558) =
        batchC02700PlusMidpointP028Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP028RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP028Rounded2558‖ ≤
          batchC02700PlusMidpointP028Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP028Factor2558
      batchC02700PlusMidpointP028Center2558)
  rw [batchC02700PlusMidpointP028RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP028Factor2558 * embedPair2542
        batchC02700PlusMidpointP028Center2558)
    (embedPair2542 batchC02700PlusMidpointP028Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP028DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP028Factor2558,
      batchC02700PlusMidpointP028Error2558, rounding2542,
      batchC02700PlusMidpointP028Radius2558]

theorem batchC02700PlusMidpointP028DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP028Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP028RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP028Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP028Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP028Rounded2558]

def batchC02700PlusMidpointP029Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700PlusMidpointP029Radius2558 : ℝ := ((2223573752513 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700PlusMidpointP029RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700PlusMidpointP029Factor2558
        batchC02700PlusMidpointP029Center2558) =
        batchC02700PlusMidpointP029Rounded2558 := by
  cbv

theorem batchC02700PlusMidpointP029RoundedError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02700PlusMidpointPosition2558 -
      embedPair2542 batchC02700PlusMidpointP029Rounded2558‖ ≤
          batchC02700PlusMidpointP029Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700PlusMidpointP029Factor2558
      batchC02700PlusMidpointP029Center2558)
  rw [batchC02700PlusMidpointP029RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP029Factor2558 * embedPair2542
        batchC02700PlusMidpointP029Center2558)
    (embedPair2542 batchC02700PlusMidpointP029Rounded2558)).trans (add_le_add
        batchC02700PlusMidpointP029DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700PlusMidpointP029Factor2558,
      batchC02700PlusMidpointP029Error2558, rounding2542,
      batchC02700PlusMidpointP029Radius2558]

theorem batchC02700PlusMidpointP029DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02700PlusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700PlusMidpoint_triangle2558
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02700PlusMidpointPosition2558)
    (embedPair2542 batchC02700PlusMidpointP029Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700PlusMidpointP029RoundedError2558
      (embedPair_magnitude2542
      batchC02700PlusMidpointP029Rounded2558))
  apply h'.trans
  norm_num [batchC02700PlusMidpointP029Radius2558, pairMagnitude2542,
      batchC02700PlusMidpointP029Rounded2558]

noncomputable def batchC02700PlusSignedMidpointValue2558 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchC02700PlusMidpointP000Rounded2558
  | 1 => embedPair2542 batchC02700PlusMidpointP001Rounded2558
  | 2 => embedPair2542 batchC02700PlusMidpointP002Rounded2558
  | 3 => embedPair2542 batchC02700PlusMidpointP003Rounded2558
  | 4 => embedPair2542 batchC02700PlusMidpointP004Rounded2558
  | 5 => embedPair2542 batchC02700PlusMidpointP005Rounded2558
  | 6 => embedPair2542 batchC02700PlusMidpointP006Rounded2558
  | 7 => embedPair2542 batchC02700PlusMidpointP007Rounded2558
  | 8 => embedPair2542 batchC02700PlusMidpointP008Rounded2558
  | 9 => embedPair2542 batchC02700PlusMidpointP009Rounded2558
  | 10 => embedPair2542 batchC02700PlusMidpointP010Rounded2558
  | 11 => embedPair2542 batchC02700PlusMidpointP011Rounded2558
  | 12 => embedPair2542 batchC02700PlusMidpointP012Rounded2558
  | 13 => embedPair2542 batchC02700PlusMidpointP013Rounded2558
  | 14 => embedPair2542 batchC02700PlusMidpointP014Rounded2558
  | 15 => embedPair2542 batchC02700PlusMidpointP015Rounded2558
  | 16 => embedPair2542 batchC02700PlusMidpointP016Rounded2558
  | 17 => embedPair2542 batchC02700PlusMidpointP017Rounded2558
  | 18 => embedPair2542 batchC02700PlusMidpointP018Rounded2558
  | 19 => embedPair2542 batchC02700PlusMidpointP019Rounded2558
  | 20 => embedPair2542 batchC02700PlusMidpointP020Rounded2558
  | 21 => embedPair2542 batchC02700PlusMidpointP021Rounded2558
  | 22 => embedPair2542 batchC02700PlusMidpointP022Rounded2558
  | 23 => embedPair2542 batchC02700PlusMidpointP023Rounded2558
  | 24 => embedPair2542 batchC02700PlusMidpointP024Rounded2558
  | 25 => embedPair2542 batchC02700PlusMidpointP025Rounded2558
  | 26 => embedPair2542 batchC02700PlusMidpointP026Rounded2558
  | 27 => embedPair2542 batchC02700PlusMidpointP027Rounded2558
  | 28 => embedPair2542 batchC02700PlusMidpointP028Rounded2558
  | 29 => embedPair2542 batchC02700PlusMidpointP029Rounded2558
  | _ => 0

noncomputable def batchC02700PlusSignedMidpointError2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02700PlusMidpointP000Radius2558
  | 1 => batchC02700PlusMidpointP001Radius2558
  | 2 => batchC02700PlusMidpointP002Radius2558
  | 3 => batchC02700PlusMidpointP003Radius2558
  | 4 => batchC02700PlusMidpointP004Radius2558
  | 5 => batchC02700PlusMidpointP005Radius2558
  | 6 => batchC02700PlusMidpointP006Radius2558
  | 7 => batchC02700PlusMidpointP007Radius2558
  | 8 => batchC02700PlusMidpointP008Radius2558
  | 9 => batchC02700PlusMidpointP009Radius2558
  | 10 => batchC02700PlusMidpointP010Radius2558
  | 11 => batchC02700PlusMidpointP011Radius2558
  | 12 => batchC02700PlusMidpointP012Radius2558
  | 13 => batchC02700PlusMidpointP013Radius2558
  | 14 => batchC02700PlusMidpointP014Radius2558
  | 15 => batchC02700PlusMidpointP015Radius2558
  | 16 => batchC02700PlusMidpointP016Radius2558
  | 17 => batchC02700PlusMidpointP017Radius2558
  | 18 => batchC02700PlusMidpointP018Radius2558
  | 19 => batchC02700PlusMidpointP019Radius2558
  | 20 => batchC02700PlusMidpointP020Radius2558
  | 21 => batchC02700PlusMidpointP021Radius2558
  | 22 => batchC02700PlusMidpointP022Radius2558
  | 23 => batchC02700PlusMidpointP023Radius2558
  | 24 => batchC02700PlusMidpointP024Radius2558
  | 25 => batchC02700PlusMidpointP025Radius2558
  | 26 => batchC02700PlusMidpointP026Radius2558
  | 27 => batchC02700PlusMidpointP027Radius2558
  | 28 => batchC02700PlusMidpointP028Radius2558
  | 29 => batchC02700PlusMidpointP029Radius2558
  | _ => 0

theorem batchC02700PlusSignedMidpointExpError2558 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02700PlusMidpointPosition2558 -
        batchC02700PlusSignedMidpointValue2558 i‖ ≤ batchC02700PlusSignedMidpointError2558 i := by
  fin_cases i
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP000RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP001RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP002RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP003RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP004RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP005RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP006RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP007RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP008RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP009RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP010RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP011RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP012RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP013RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP014RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP015RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP016RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP017RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP018RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP019RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP020RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP021RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP022RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP023RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP024RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP025RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP026RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP027RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP028RoundedError2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP029RoundedError2558

theorem batchC02700PlusSignedMidpointUnitNorm2558 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02700PlusMidpointPosition2558‖ ≤ 1 :=
        by
  fin_cases i
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP000DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP001DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP002DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP003DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP004DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP005DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP006DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP007DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP008DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP009DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP010DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP011DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP012DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP013DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP014DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP015DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP016DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP017DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP018DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP019DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP020DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP021DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP022DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP023DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP024DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP025DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP026DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP027DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP028DerivativeNorm2558
  · simpa only [batchC02700PlusSignedMidpointValue2558, batchC02700PlusSignedMidpointError2558]
      using
      batchC02700PlusMidpointP029DerivativeNorm2558

noncomputable def batchC02700PlusSignedMidpointSum2558 : ℂ := ⟨(((-(((3799 * 10^40
        + 6685605077440837126035958386636642668854) * 10^40
        + 3067130214842208459058169478650349255097) * 10^40
        + 7228261301618323694781161573608753856707)) : ℝ) /
        (((21661481 * 10^40
        + 9853188660904563608136178414330971646513) * 10^40
        + 7356699351937172355172896723145017999980) * 10^40
        + 47688590453885868835635965404913860608)),
    (((-(((131 * 10^40
        + 5058006603608054653560648572876380667654) * 10^40
        + 6463026732528082206085874357707970195372) * 10^40
        + 8033968005117630904243217967921675496395)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216))⟩

noncomputable def batchC02700PlusSignedMidpointUpper2558 : ℝ := ((8777 : ℝ) /
        50000000)

theorem batchC02700PlusSignedMidpointSum_eq2558 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02700PlusSignedMidpointValue2558 i) =
      batchC02700PlusSignedMidpointSum2558 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
        batchC02700PlusSignedMidpointValue2558,
      batchC02700PlusSignedMidpointSum2558, embedPair2542, batchC02700PlusMidpointP000Rounded2558,
      batchC02700PlusMidpointP001Rounded2558,
      batchC02700PlusMidpointP002Rounded2558,
      batchC02700PlusMidpointP003Rounded2558,
      batchC02700PlusMidpointP004Rounded2558,
      batchC02700PlusMidpointP005Rounded2558,
      batchC02700PlusMidpointP006Rounded2558,
      batchC02700PlusMidpointP007Rounded2558,
      batchC02700PlusMidpointP008Rounded2558,
      batchC02700PlusMidpointP009Rounded2558,
      batchC02700PlusMidpointP010Rounded2558,
      batchC02700PlusMidpointP011Rounded2558,
      batchC02700PlusMidpointP012Rounded2558,
      batchC02700PlusMidpointP013Rounded2558,
      batchC02700PlusMidpointP014Rounded2558,
      batchC02700PlusMidpointP015Rounded2558,
      batchC02700PlusMidpointP016Rounded2558,
      batchC02700PlusMidpointP017Rounded2558,
      batchC02700PlusMidpointP018Rounded2558,
      batchC02700PlusMidpointP019Rounded2558,
      batchC02700PlusMidpointP020Rounded2558,
      batchC02700PlusMidpointP021Rounded2558,
      batchC02700PlusMidpointP022Rounded2558,
      batchC02700PlusMidpointP023Rounded2558,
      batchC02700PlusMidpointP024Rounded2558,
      batchC02700PlusMidpointP025Rounded2558,
      batchC02700PlusMidpointP026Rounded2558,
      batchC02700PlusMidpointP027Rounded2558,
      batchC02700PlusMidpointP028Rounded2558,
      batchC02700PlusMidpointP029Rounded2558, Complex.mul_re, Complex.mul_im]

theorem batchC02700PlusSignedMidpointSum_norm2558 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02700PlusSignedMidpointValue2558 i‖ ≤
        ((2193 : ℝ) /
        12500000) := by
  rw [batchC02700PlusSignedMidpointSum_eq2558]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchC02700PlusSignedMidpointSum2558]

theorem batchC02700PlusSignedMidpointCharge2558 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchC02700PlusSignedMidpointError2558 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
      batchC02700PlusSignedMidpointError2558,
      batchC02700PlusMidpointP000Radius2558,
      batchC02700PlusMidpointP001Radius2558,
      batchC02700PlusMidpointP002Radius2558,
      batchC02700PlusMidpointP003Radius2558,
      batchC02700PlusMidpointP004Radius2558,
      batchC02700PlusMidpointP005Radius2558,
      batchC02700PlusMidpointP006Radius2558,
      batchC02700PlusMidpointP007Radius2558,
      batchC02700PlusMidpointP008Radius2558,
      batchC02700PlusMidpointP009Radius2558,
      batchC02700PlusMidpointP010Radius2558,
      batchC02700PlusMidpointP011Radius2558,
      batchC02700PlusMidpointP012Radius2558,
      batchC02700PlusMidpointP013Radius2558,
      batchC02700PlusMidpointP014Radius2558,
      batchC02700PlusMidpointP015Radius2558,
      batchC02700PlusMidpointP016Radius2558,
      batchC02700PlusMidpointP017Radius2558,
      batchC02700PlusMidpointP018Radius2558,
      batchC02700PlusMidpointP019Radius2558,
      batchC02700PlusMidpointP020Radius2558,
      batchC02700PlusMidpointP021Radius2558,
      batchC02700PlusMidpointP022Radius2558,
      batchC02700PlusMidpointP023Radius2558,
      batchC02700PlusMidpointP024Radius2558,
      batchC02700PlusMidpointP025Radius2558,
      batchC02700PlusMidpointP026Radius2558,
      batchC02700PlusMidpointP027Radius2558,
      batchC02700PlusMidpointP028Radius2558,
      batchC02700PlusMidpointP029Radius2558]

theorem batchC02700PlusSignedMidpointUpper_le2558 :
    signedJetUpper2539 2 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchC02700PlusMidpointPosition2558 ≤
          batchC02700PlusSignedMidpointUpper2558 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02700PlusMidpointPosition2558‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02700PlusSignedMidpointValue2558 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchC02700PlusSignedMidpointError2558 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (batchC02700PlusSignedMidpointExpError2558 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02700PlusMidpointPosition2558‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchC02700PlusSignedMidpointUnitNorm2558 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02700PlusMidpointPosition2558‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchC02700PlusSignedMidpointUpper2558
  linarith [batchC02700PlusSignedMidpointSum_norm2558, batchC02700PlusSignedMidpointCharge2558]

theorem batchC02700PlusPhysicalSecond2558 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        batchC02700PlusMidpointPosition2558‖ ≤
      batchC02700PlusSignedMidpointUpper2558 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchC02700PlusMidpointPosition2558
  exact h.trans batchC02700PlusSignedMidpointUpper_le2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02700PlusSignedMidpointExpError2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusSignedMidpointSum_eq2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusSignedMidpointCharge2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusSignedMidpointUpper_le2558
#print axioms ConnesWeilRH.Dev.batchC02700PlusPhysicalSecond2558
