import ConnesWeilRH.Dev.C1RouteABatchC02700MinusMidpoint2558

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem batchC02700MinusMidpoint_triangle2558 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def batchC02700MinusMidpointP000Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP000Radius2558 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02700MinusMidpointP000RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP000Factor2558
        batchC02700MinusMidpointP000Center2558) =
        batchC02700MinusMidpointP000Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP000RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP000Rounded2558‖ ≤
          batchC02700MinusMidpointP000Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP000Factor2558
      batchC02700MinusMidpointP000Center2558)
  rw [batchC02700MinusMidpointP000RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP000Factor2558 * embedPair2542
        batchC02700MinusMidpointP000Center2558)
    (embedPair2542 batchC02700MinusMidpointP000Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP000DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP000Factor2558,
      batchC02700MinusMidpointP000Error2558, rounding2542,
      batchC02700MinusMidpointP000Radius2558]

theorem batchC02700MinusMidpointP000DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP000Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP000RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP000Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP000Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP000Rounded2558]

def batchC02700MinusMidpointP001Rounded2558 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP001Radius2558 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP001RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP001Factor2558
        batchC02700MinusMidpointP001Center2558) =
        batchC02700MinusMidpointP001Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP001RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP001Rounded2558‖ ≤
          batchC02700MinusMidpointP001Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP001Factor2558
      batchC02700MinusMidpointP001Center2558)
  rw [batchC02700MinusMidpointP001RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP001Factor2558 * embedPair2542
        batchC02700MinusMidpointP001Center2558)
    (embedPair2542 batchC02700MinusMidpointP001Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP001DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP001Factor2558,
      batchC02700MinusMidpointP001Error2558, rounding2542,
      batchC02700MinusMidpointP001Radius2558]

theorem batchC02700MinusMidpointP001DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP001Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP001RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP001Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP001Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP001Rounded2558]

def batchC02700MinusMidpointP002Rounded2558 : RatPair2542 :=
  (((14734133 : ℚ) /
        633825300114114700748351602688),
    (((-21944745) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02700MinusMidpointP002Radius2558 : ℝ := ((2199023393955 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP002RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP002Factor2558
        batchC02700MinusMidpointP002Center2558) =
        batchC02700MinusMidpointP002Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP002RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP002Rounded2558‖ ≤
          batchC02700MinusMidpointP002Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP002Factor2558
      batchC02700MinusMidpointP002Center2558)
  rw [batchC02700MinusMidpointP002RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP002Factor2558 * embedPair2542
        batchC02700MinusMidpointP002Center2558)
    (embedPair2542 batchC02700MinusMidpointP002Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP002DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP002Factor2558,
      batchC02700MinusMidpointP002Error2558, rounding2542,
      batchC02700MinusMidpointP002Radius2558]

theorem batchC02700MinusMidpointP002DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP002Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP002RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP002Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP002Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP002Rounded2558]

def batchC02700MinusMidpointP003Rounded2558 : RatPair2542 :=
  (((332377269281621 : ℚ) /
        1267650600228229401496703205376),
    ((48890259578371 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC02700MinusMidpointP003Radius2558 : ℝ := ((3870929946619 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP003RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP003Factor2558
        batchC02700MinusMidpointP003Center2558) =
        batchC02700MinusMidpointP003Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP003RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP003Rounded2558‖ ≤
          batchC02700MinusMidpointP003Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP003Factor2558
      batchC02700MinusMidpointP003Center2558)
  rw [batchC02700MinusMidpointP003RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP003Factor2558 * embedPair2542
        batchC02700MinusMidpointP003Center2558)
    (embedPair2542 batchC02700MinusMidpointP003Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP003DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP003Factor2558,
      batchC02700MinusMidpointP003Error2558, rounding2542,
      batchC02700MinusMidpointP003Radius2558]

theorem batchC02700MinusMidpointP003DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP003Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP003RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP003Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP003Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP003Rounded2558]

def batchC02700MinusMidpointP004Rounded2558 : RatPair2542 :=
  (((129302948675881649 : ℚ) /
        1267650600228229401496703205376),
    (((-92927573240012739) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02700MinusMidpointP004Radius2558 : ℝ := ((681893315266257 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP004RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP004Factor2558
        batchC02700MinusMidpointP004Center2558) =
        batchC02700MinusMidpointP004Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP004RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP004Rounded2558‖ ≤
          batchC02700MinusMidpointP004Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP004Factor2558
      batchC02700MinusMidpointP004Center2558)
  rw [batchC02700MinusMidpointP004RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP004Factor2558 * embedPair2542
        batchC02700MinusMidpointP004Center2558)
    (embedPair2542 batchC02700MinusMidpointP004Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP004DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP004Factor2558,
      batchC02700MinusMidpointP004Error2558, rounding2542,
      batchC02700MinusMidpointP004Radius2558]

theorem batchC02700MinusMidpointP004DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP004Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP004RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP004Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP004Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP004Rounded2558]

def batchC02700MinusMidpointP005Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP005Radius2558 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02700MinusMidpointP005RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP005Factor2558
        batchC02700MinusMidpointP005Center2558) =
        batchC02700MinusMidpointP005Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP005RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP005Rounded2558‖ ≤
          batchC02700MinusMidpointP005Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP005Factor2558
      batchC02700MinusMidpointP005Center2558)
  rw [batchC02700MinusMidpointP005RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP005Factor2558 * embedPair2542
        batchC02700MinusMidpointP005Center2558)
    (embedPair2542 batchC02700MinusMidpointP005Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP005DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP005Factor2558,
      batchC02700MinusMidpointP005Error2558, rounding2542,
      batchC02700MinusMidpointP005Radius2558]

theorem batchC02700MinusMidpointP005DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP005Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP005RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP005Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP005Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP005Rounded2558]

def batchC02700MinusMidpointP006Rounded2558 : RatPair2542 :=
  (((11 : ℚ) /
        158456325028528675187087900672),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP006Radius2558 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP006RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP006Factor2558
        batchC02700MinusMidpointP006Center2558) =
        batchC02700MinusMidpointP006Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP006RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP006Rounded2558‖ ≤
          batchC02700MinusMidpointP006Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP006Factor2558
      batchC02700MinusMidpointP006Center2558)
  rw [batchC02700MinusMidpointP006RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP006Factor2558 * embedPair2542
        batchC02700MinusMidpointP006Center2558)
    (embedPair2542 batchC02700MinusMidpointP006Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP006DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP006Factor2558,
      batchC02700MinusMidpointP006Error2558, rounding2542,
      batchC02700MinusMidpointP006Radius2558]

theorem batchC02700MinusMidpointP006DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP006Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP006RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP006Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP006Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP006Rounded2558]

def batchC02700MinusMidpointP007Rounded2558 : RatPair2542 :=
  (((17651353462899 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP007Radius2558 : ℝ := ((1101954945631 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02700MinusMidpointP007RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP007Factor2558
        batchC02700MinusMidpointP007Center2558) =
        batchC02700MinusMidpointP007Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP007RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP007Rounded2558‖ ≤
          batchC02700MinusMidpointP007Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP007Factor2558
      batchC02700MinusMidpointP007Center2558)
  rw [batchC02700MinusMidpointP007RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP007Factor2558 * embedPair2542
        batchC02700MinusMidpointP007Center2558)
    (embedPair2542 batchC02700MinusMidpointP007Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP007DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP007Factor2558,
      batchC02700MinusMidpointP007Error2558, rounding2542,
      batchC02700MinusMidpointP007Radius2558]

theorem batchC02700MinusMidpointP007DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP007Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP007RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP007Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP007Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP007Rounded2558]

def batchC02700MinusMidpointP008Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP008Radius2558 : ℝ := ((2223573723861 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP008RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP008Factor2558
        batchC02700MinusMidpointP008Center2558) =
        batchC02700MinusMidpointP008Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP008RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP008Rounded2558‖ ≤
          batchC02700MinusMidpointP008Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP008Factor2558
      batchC02700MinusMidpointP008Center2558)
  rw [batchC02700MinusMidpointP008RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP008Factor2558 * embedPair2542
        batchC02700MinusMidpointP008Center2558)
    (embedPair2542 batchC02700MinusMidpointP008Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP008DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP008Factor2558,
      batchC02700MinusMidpointP008Error2558, rounding2542,
      batchC02700MinusMidpointP008Radius2558]

theorem batchC02700MinusMidpointP008DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP008Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP008RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP008Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP008Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP008Rounded2558]

def batchC02700MinusMidpointP009Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP009Radius2558 : ℝ := ((2223573726841 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP009RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP009Factor2558
        batchC02700MinusMidpointP009Center2558) =
        batchC02700MinusMidpointP009Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP009RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP009Rounded2558‖ ≤
          batchC02700MinusMidpointP009Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP009Factor2558
      batchC02700MinusMidpointP009Center2558)
  rw [batchC02700MinusMidpointP009RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP009Factor2558 * embedPair2542
        batchC02700MinusMidpointP009Center2558)
    (embedPair2542 batchC02700MinusMidpointP009Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP009DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP009Factor2558,
      batchC02700MinusMidpointP009Error2558, rounding2542,
      batchC02700MinusMidpointP009Radius2558]

theorem batchC02700MinusMidpointP009DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP009Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP009RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP009Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP009Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP009Rounded2558]

def batchC02700MinusMidpointP010Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP010Radius2558 : ℝ := ((277946716071 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02700MinusMidpointP010RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP010Factor2558
        batchC02700MinusMidpointP010Center2558) =
        batchC02700MinusMidpointP010Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP010RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP010Rounded2558‖ ≤
          batchC02700MinusMidpointP010Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP010Factor2558
      batchC02700MinusMidpointP010Center2558)
  rw [batchC02700MinusMidpointP010RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP010Factor2558 * embedPair2542
        batchC02700MinusMidpointP010Center2558)
    (embedPair2542 batchC02700MinusMidpointP010Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP010DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP010Factor2558,
      batchC02700MinusMidpointP010Error2558, rounding2542,
      batchC02700MinusMidpointP010Radius2558]

theorem batchC02700MinusMidpointP010DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP010Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP010RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP010Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP010Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP010Rounded2558]

def batchC02700MinusMidpointP011Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP011Radius2558 : ℝ := ((2223573729719 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP011RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP011Factor2558
        batchC02700MinusMidpointP011Center2558) =
        batchC02700MinusMidpointP011Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP011RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP011Rounded2558‖ ≤
          batchC02700MinusMidpointP011Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP011Factor2558
      batchC02700MinusMidpointP011Center2558)
  rw [batchC02700MinusMidpointP011RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP011Factor2558 * embedPair2542
        batchC02700MinusMidpointP011Center2558)
    (embedPair2542 batchC02700MinusMidpointP011Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP011DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP011Factor2558,
      batchC02700MinusMidpointP011Error2558, rounding2542,
      batchC02700MinusMidpointP011Radius2558]

theorem batchC02700MinusMidpointP011DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP011Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP011RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP011Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP011Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP011Rounded2558]

def batchC02700MinusMidpointP012Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP012Radius2558 : ℝ := ((2223573730911 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP012RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP012Factor2558
        batchC02700MinusMidpointP012Center2558) =
        batchC02700MinusMidpointP012Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP012RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP012Rounded2558‖ ≤
          batchC02700MinusMidpointP012Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP012Factor2558
      batchC02700MinusMidpointP012Center2558)
  rw [batchC02700MinusMidpointP012RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP012Factor2558 * embedPair2542
        batchC02700MinusMidpointP012Center2558)
    (embedPair2542 batchC02700MinusMidpointP012Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP012DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP012Factor2558,
      batchC02700MinusMidpointP012Error2558, rounding2542,
      batchC02700MinusMidpointP012Radius2558]

theorem batchC02700MinusMidpointP012DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP012Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP012RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP012Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP012Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP012Rounded2558]

def batchC02700MinusMidpointP013Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP013Radius2558 : ℝ := ((2223573731997 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP013RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP013Factor2558
        batchC02700MinusMidpointP013Center2558) =
        batchC02700MinusMidpointP013Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP013RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP013Rounded2558‖ ≤
          batchC02700MinusMidpointP013Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP013Factor2558
      batchC02700MinusMidpointP013Center2558)
  rw [batchC02700MinusMidpointP013RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP013Factor2558 * embedPair2542
        batchC02700MinusMidpointP013Center2558)
    (embedPair2542 batchC02700MinusMidpointP013Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP013DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP013Factor2558,
      batchC02700MinusMidpointP013Error2558, rounding2542,
      batchC02700MinusMidpointP013Radius2558]

theorem batchC02700MinusMidpointP013DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP013Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP013RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP013Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP013Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP013Rounded2558]

def batchC02700MinusMidpointP014Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP014Radius2558 : ℝ := ((1111786867005 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02700MinusMidpointP014RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP014Factor2558
        batchC02700MinusMidpointP014Center2558) =
        batchC02700MinusMidpointP014Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP014RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP014Rounded2558‖ ≤
          batchC02700MinusMidpointP014Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP014Factor2558
      batchC02700MinusMidpointP014Center2558)
  rw [batchC02700MinusMidpointP014RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP014Factor2558 * embedPair2542
        batchC02700MinusMidpointP014Center2558)
    (embedPair2542 batchC02700MinusMidpointP014Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP014DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP014Factor2558,
      batchC02700MinusMidpointP014Error2558, rounding2542,
      batchC02700MinusMidpointP014Radius2558]

theorem batchC02700MinusMidpointP014DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP014Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP014RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP014Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP014Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP014Rounded2558]

def batchC02700MinusMidpointP015Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP015Radius2558 : ℝ := ((2223573735453 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP015RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP015Factor2558
        batchC02700MinusMidpointP015Center2558) =
        batchC02700MinusMidpointP015Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP015RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP015Rounded2558‖ ≤
          batchC02700MinusMidpointP015Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP015Factor2558
      batchC02700MinusMidpointP015Center2558)
  rw [batchC02700MinusMidpointP015RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP015Factor2558 * embedPair2542
        batchC02700MinusMidpointP015Center2558)
    (embedPair2542 batchC02700MinusMidpointP015Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP015DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP015Factor2558,
      batchC02700MinusMidpointP015Error2558, rounding2542,
      batchC02700MinusMidpointP015Radius2558]

theorem batchC02700MinusMidpointP015DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP015Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP015RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP015Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP015Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP015Rounded2558]

def batchC02700MinusMidpointP016Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP016Radius2558 : ℝ := ((2223573736495 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP016RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP016Factor2558
        batchC02700MinusMidpointP016Center2558) =
        batchC02700MinusMidpointP016Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP016RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP016Rounded2558‖ ≤
          batchC02700MinusMidpointP016Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP016Factor2558
      batchC02700MinusMidpointP016Center2558)
  rw [batchC02700MinusMidpointP016RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP016Factor2558 * embedPair2542
        batchC02700MinusMidpointP016Center2558)
    (embedPair2542 batchC02700MinusMidpointP016Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP016DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP016Factor2558,
      batchC02700MinusMidpointP016Error2558, rounding2542,
      batchC02700MinusMidpointP016Radius2558]

theorem batchC02700MinusMidpointP016DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP016Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP016RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP016Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP016Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP016Rounded2558]

def batchC02700MinusMidpointP017Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP017Radius2558 : ℝ := ((2223573738519 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP017RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP017Factor2558
        batchC02700MinusMidpointP017Center2558) =
        batchC02700MinusMidpointP017Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP017RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP017Rounded2558‖ ≤
          batchC02700MinusMidpointP017Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP017Factor2558
      batchC02700MinusMidpointP017Center2558)
  rw [batchC02700MinusMidpointP017RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP017Factor2558 * embedPair2542
        batchC02700MinusMidpointP017Center2558)
    (embedPair2542 batchC02700MinusMidpointP017Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP017DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP017Factor2558,
      batchC02700MinusMidpointP017Error2558, rounding2542,
      batchC02700MinusMidpointP017Radius2558]

theorem batchC02700MinusMidpointP017DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP017Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP017RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP017Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP017Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP017Rounded2558]

def batchC02700MinusMidpointP018Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP018Radius2558 : ℝ := ((2223573739285 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP018RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP018Factor2558
        batchC02700MinusMidpointP018Center2558) =
        batchC02700MinusMidpointP018Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP018RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP018Rounded2558‖ ≤
          batchC02700MinusMidpointP018Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP018Factor2558
      batchC02700MinusMidpointP018Center2558)
  rw [batchC02700MinusMidpointP018RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP018Factor2558 * embedPair2542
        batchC02700MinusMidpointP018Center2558)
    (embedPair2542 batchC02700MinusMidpointP018Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP018DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP018Factor2558,
      batchC02700MinusMidpointP018Error2558, rounding2542,
      batchC02700MinusMidpointP018Radius2558]

theorem batchC02700MinusMidpointP018DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP018Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP018RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP018Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP018Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP018Rounded2558]

def batchC02700MinusMidpointP019Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP019Radius2558 : ℝ := ((555893435167 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02700MinusMidpointP019RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP019Factor2558
        batchC02700MinusMidpointP019Center2558) =
        batchC02700MinusMidpointP019Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP019RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP019Rounded2558‖ ≤
          batchC02700MinusMidpointP019Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP019Factor2558
      batchC02700MinusMidpointP019Center2558)
  rw [batchC02700MinusMidpointP019RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP019Factor2558 * embedPair2542
        batchC02700MinusMidpointP019Center2558)
    (embedPair2542 batchC02700MinusMidpointP019Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP019DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP019Factor2558,
      batchC02700MinusMidpointP019Error2558, rounding2542,
      batchC02700MinusMidpointP019Radius2558]

theorem batchC02700MinusMidpointP019DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP019Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP019RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP019Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP019Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP019Rounded2558]

def batchC02700MinusMidpointP020Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP020Radius2558 : ℝ := ((2223573742173 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP020RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP020Factor2558
        batchC02700MinusMidpointP020Center2558) =
        batchC02700MinusMidpointP020Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP020RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP020Rounded2558‖ ≤
          batchC02700MinusMidpointP020Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP020Factor2558
      batchC02700MinusMidpointP020Center2558)
  rw [batchC02700MinusMidpointP020RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP020Factor2558 * embedPair2542
        batchC02700MinusMidpointP020Center2558)
    (embedPair2542 batchC02700MinusMidpointP020Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP020DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP020Factor2558,
      batchC02700MinusMidpointP020Error2558, rounding2542,
      batchC02700MinusMidpointP020Radius2558]

theorem batchC02700MinusMidpointP020DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP020Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP020RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP020Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP020Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP020Rounded2558]

def batchC02700MinusMidpointP021Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP021Radius2558 : ℝ := ((555893435857 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02700MinusMidpointP021RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP021Factor2558
        batchC02700MinusMidpointP021Center2558) =
        batchC02700MinusMidpointP021Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP021RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP021Rounded2558‖ ≤
          batchC02700MinusMidpointP021Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP021Factor2558
      batchC02700MinusMidpointP021Center2558)
  rw [batchC02700MinusMidpointP021RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP021Factor2558 * embedPair2542
        batchC02700MinusMidpointP021Center2558)
    (embedPair2542 batchC02700MinusMidpointP021Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP021DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP021Factor2558,
      batchC02700MinusMidpointP021Error2558, rounding2542,
      batchC02700MinusMidpointP021Radius2558]

theorem batchC02700MinusMidpointP021DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP021Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP021RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP021Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP021Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP021Rounded2558]

def batchC02700MinusMidpointP022Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP022Radius2558 : ℝ := ((2223573744071 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP022RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP022Factor2558
        batchC02700MinusMidpointP022Center2558) =
        batchC02700MinusMidpointP022Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP022RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP022Rounded2558‖ ≤
          batchC02700MinusMidpointP022Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP022Factor2558
      batchC02700MinusMidpointP022Center2558)
  rw [batchC02700MinusMidpointP022RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP022Factor2558 * embedPair2542
        batchC02700MinusMidpointP022Center2558)
    (embedPair2542 batchC02700MinusMidpointP022Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP022DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP022Factor2558,
      batchC02700MinusMidpointP022Error2558, rounding2542,
      batchC02700MinusMidpointP022Radius2558]

theorem batchC02700MinusMidpointP022DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP022Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP022RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP022Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP022Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP022Rounded2558]

def batchC02700MinusMidpointP023Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP023Radius2558 : ℝ := ((2223573745923 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP023RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP023Factor2558
        batchC02700MinusMidpointP023Center2558) =
        batchC02700MinusMidpointP023Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP023RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP023Rounded2558‖ ≤
          batchC02700MinusMidpointP023Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP023Factor2558
      batchC02700MinusMidpointP023Center2558)
  rw [batchC02700MinusMidpointP023RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP023Factor2558 * embedPair2542
        batchC02700MinusMidpointP023Center2558)
    (embedPair2542 batchC02700MinusMidpointP023Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP023DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP023Factor2558,
      batchC02700MinusMidpointP023Error2558, rounding2542,
      batchC02700MinusMidpointP023Radius2558]

theorem batchC02700MinusMidpointP023DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP023Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP023RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP023Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP023Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP023Rounded2558]

def batchC02700MinusMidpointP024Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP024Radius2558 : ℝ := ((2223573746775 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP024RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP024Factor2558
        batchC02700MinusMidpointP024Center2558) =
        batchC02700MinusMidpointP024Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP024RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP024Rounded2558‖ ≤
          batchC02700MinusMidpointP024Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP024Factor2558
      batchC02700MinusMidpointP024Center2558)
  rw [batchC02700MinusMidpointP024RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP024Factor2558 * embedPair2542
        batchC02700MinusMidpointP024Center2558)
    (embedPair2542 batchC02700MinusMidpointP024Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP024DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP024Factor2558,
      batchC02700MinusMidpointP024Error2558, rounding2542,
      batchC02700MinusMidpointP024Radius2558]

theorem batchC02700MinusMidpointP024DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP024Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP024RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP024Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP024Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP024Rounded2558]

def batchC02700MinusMidpointP025Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP025Radius2558 : ℝ := ((1111786873921 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02700MinusMidpointP025RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP025Factor2558
        batchC02700MinusMidpointP025Center2558) =
        batchC02700MinusMidpointP025Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP025RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP025Rounded2558‖ ≤
          batchC02700MinusMidpointP025Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP025Factor2558
      batchC02700MinusMidpointP025Center2558)
  rw [batchC02700MinusMidpointP025RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP025Factor2558 * embedPair2542
        batchC02700MinusMidpointP025Center2558)
    (embedPair2542 batchC02700MinusMidpointP025Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP025DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP025Factor2558,
      batchC02700MinusMidpointP025Error2558, rounding2542,
      batchC02700MinusMidpointP025Radius2558]

theorem batchC02700MinusMidpointP025DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP025Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP025RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP025Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP025Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP025Rounded2558]

def batchC02700MinusMidpointP026Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP026Radius2558 : ℝ := ((2223573748933 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP026RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP026Factor2558
        batchC02700MinusMidpointP026Center2558) =
        batchC02700MinusMidpointP026Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP026RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP026Rounded2558‖ ≤
          batchC02700MinusMidpointP026Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP026Factor2558
      batchC02700MinusMidpointP026Center2558)
  rw [batchC02700MinusMidpointP026RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP026Factor2558 * embedPair2542
        batchC02700MinusMidpointP026Center2558)
    (embedPair2542 batchC02700MinusMidpointP026Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP026DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP026Factor2558,
      batchC02700MinusMidpointP026Error2558, rounding2542,
      batchC02700MinusMidpointP026Radius2558]

theorem batchC02700MinusMidpointP026DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP026Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP026RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP026Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP026Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP026Rounded2558]

def batchC02700MinusMidpointP027Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP027Radius2558 : ℝ := ((555893437627 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02700MinusMidpointP027RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP027Factor2558
        batchC02700MinusMidpointP027Center2558) =
        batchC02700MinusMidpointP027Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP027RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP027Rounded2558‖ ≤
          batchC02700MinusMidpointP027Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP027Factor2558
      batchC02700MinusMidpointP027Center2558)
  rw [batchC02700MinusMidpointP027RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP027Factor2558 * embedPair2542
        batchC02700MinusMidpointP027Center2558)
    (embedPair2542 batchC02700MinusMidpointP027Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP027DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP027Factor2558,
      batchC02700MinusMidpointP027Error2558, rounding2542,
      batchC02700MinusMidpointP027Radius2558]

theorem batchC02700MinusMidpointP027DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP027Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP027RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP027Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP027Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP027Rounded2558]

def batchC02700MinusMidpointP028Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP028Radius2558 : ℝ := ((2223573751131 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02700MinusMidpointP028RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP028Factor2558
        batchC02700MinusMidpointP028Center2558) =
        batchC02700MinusMidpointP028Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP028RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP028Rounded2558‖ ≤
          batchC02700MinusMidpointP028Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP028Factor2558
      batchC02700MinusMidpointP028Center2558)
  rw [batchC02700MinusMidpointP028RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP028Factor2558 * embedPair2542
        batchC02700MinusMidpointP028Center2558)
    (embedPair2542 batchC02700MinusMidpointP028Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP028DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP028Factor2558,
      batchC02700MinusMidpointP028Error2558, rounding2542,
      batchC02700MinusMidpointP028Radius2558]

theorem batchC02700MinusMidpointP028DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP028Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP028RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP028Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP028Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP028Rounded2558]

def batchC02700MinusMidpointP029Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02700MinusMidpointP029Radius2558 : ℝ := ((138973359505 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem batchC02700MinusMidpointP029RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02700MinusMidpointP029Factor2558
        batchC02700MinusMidpointP029Center2558) =
        batchC02700MinusMidpointP029Rounded2558 := by
  cbv

theorem batchC02700MinusMidpointP029RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02700MinusMidpointPosition2558 -
      embedPair2542 batchC02700MinusMidpointP029Rounded2558‖ ≤
          batchC02700MinusMidpointP029Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02700MinusMidpointP029Factor2558
      batchC02700MinusMidpointP029Center2558)
  rw [batchC02700MinusMidpointP029RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP029Factor2558 * embedPair2542
        batchC02700MinusMidpointP029Center2558)
    (embedPair2542 batchC02700MinusMidpointP029Rounded2558)).trans (add_le_add
        batchC02700MinusMidpointP029DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02700MinusMidpointP029Factor2558,
      batchC02700MinusMidpointP029Error2558, rounding2542,
      batchC02700MinusMidpointP029Radius2558]

theorem batchC02700MinusMidpointP029DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02700MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02700MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02700MinusMidpointPosition2558)
    (embedPair2542 batchC02700MinusMidpointP029Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02700MinusMidpointP029RoundedError2558
      (embedPair_magnitude2542
      batchC02700MinusMidpointP029Rounded2558))
  apply h'.trans
  norm_num [batchC02700MinusMidpointP029Radius2558, pairMagnitude2542,
      batchC02700MinusMidpointP029Rounded2558]

noncomputable def batchC02700MinusSignedMidpointValue2558 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchC02700MinusMidpointP000Rounded2558
  | 1 => embedPair2542 batchC02700MinusMidpointP001Rounded2558
  | 2 => embedPair2542 batchC02700MinusMidpointP002Rounded2558
  | 3 => embedPair2542 batchC02700MinusMidpointP003Rounded2558
  | 4 => embedPair2542 batchC02700MinusMidpointP004Rounded2558
  | 5 => embedPair2542 batchC02700MinusMidpointP005Rounded2558
  | 6 => embedPair2542 batchC02700MinusMidpointP006Rounded2558
  | 7 => embedPair2542 batchC02700MinusMidpointP007Rounded2558
  | 8 => embedPair2542 batchC02700MinusMidpointP008Rounded2558
  | 9 => embedPair2542 batchC02700MinusMidpointP009Rounded2558
  | 10 => embedPair2542 batchC02700MinusMidpointP010Rounded2558
  | 11 => embedPair2542 batchC02700MinusMidpointP011Rounded2558
  | 12 => embedPair2542 batchC02700MinusMidpointP012Rounded2558
  | 13 => embedPair2542 batchC02700MinusMidpointP013Rounded2558
  | 14 => embedPair2542 batchC02700MinusMidpointP014Rounded2558
  | 15 => embedPair2542 batchC02700MinusMidpointP015Rounded2558
  | 16 => embedPair2542 batchC02700MinusMidpointP016Rounded2558
  | 17 => embedPair2542 batchC02700MinusMidpointP017Rounded2558
  | 18 => embedPair2542 batchC02700MinusMidpointP018Rounded2558
  | 19 => embedPair2542 batchC02700MinusMidpointP019Rounded2558
  | 20 => embedPair2542 batchC02700MinusMidpointP020Rounded2558
  | 21 => embedPair2542 batchC02700MinusMidpointP021Rounded2558
  | 22 => embedPair2542 batchC02700MinusMidpointP022Rounded2558
  | 23 => embedPair2542 batchC02700MinusMidpointP023Rounded2558
  | 24 => embedPair2542 batchC02700MinusMidpointP024Rounded2558
  | 25 => embedPair2542 batchC02700MinusMidpointP025Rounded2558
  | 26 => embedPair2542 batchC02700MinusMidpointP026Rounded2558
  | 27 => embedPair2542 batchC02700MinusMidpointP027Rounded2558
  | 28 => embedPair2542 batchC02700MinusMidpointP028Rounded2558
  | 29 => embedPair2542 batchC02700MinusMidpointP029Rounded2558
  | _ => 0

noncomputable def batchC02700MinusSignedMidpointError2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02700MinusMidpointP000Radius2558
  | 1 => batchC02700MinusMidpointP001Radius2558
  | 2 => batchC02700MinusMidpointP002Radius2558
  | 3 => batchC02700MinusMidpointP003Radius2558
  | 4 => batchC02700MinusMidpointP004Radius2558
  | 5 => batchC02700MinusMidpointP005Radius2558
  | 6 => batchC02700MinusMidpointP006Radius2558
  | 7 => batchC02700MinusMidpointP007Radius2558
  | 8 => batchC02700MinusMidpointP008Radius2558
  | 9 => batchC02700MinusMidpointP009Radius2558
  | 10 => batchC02700MinusMidpointP010Radius2558
  | 11 => batchC02700MinusMidpointP011Radius2558
  | 12 => batchC02700MinusMidpointP012Radius2558
  | 13 => batchC02700MinusMidpointP013Radius2558
  | 14 => batchC02700MinusMidpointP014Radius2558
  | 15 => batchC02700MinusMidpointP015Radius2558
  | 16 => batchC02700MinusMidpointP016Radius2558
  | 17 => batchC02700MinusMidpointP017Radius2558
  | 18 => batchC02700MinusMidpointP018Radius2558
  | 19 => batchC02700MinusMidpointP019Radius2558
  | 20 => batchC02700MinusMidpointP020Radius2558
  | 21 => batchC02700MinusMidpointP021Radius2558
  | 22 => batchC02700MinusMidpointP022Radius2558
  | 23 => batchC02700MinusMidpointP023Radius2558
  | 24 => batchC02700MinusMidpointP024Radius2558
  | 25 => batchC02700MinusMidpointP025Radius2558
  | 26 => batchC02700MinusMidpointP026Radius2558
  | 27 => batchC02700MinusMidpointP027Radius2558
  | 28 => batchC02700MinusMidpointP028Radius2558
  | 29 => batchC02700MinusMidpointP029Radius2558
  | _ => 0

theorem batchC02700MinusSignedMidpointExpError2558 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02700MinusMidpointPosition2558 -
        batchC02700MinusSignedMidpointValue2558 i‖ ≤ batchC02700MinusSignedMidpointError2558 i :=
            by
  fin_cases i
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP000RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP001RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP002RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP003RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP004RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP005RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP006RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP007RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP008RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP009RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP010RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP011RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP012RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP013RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP014RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP015RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP016RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP017RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP018RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP019RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP020RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP021RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP022RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP023RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP024RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP025RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP026RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP027RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP028RoundedError2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP029RoundedError2558

theorem batchC02700MinusSignedMidpointUnitNorm2558 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02700MinusMidpointPosition2558‖ ≤ 1
        := by
  fin_cases i
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP000DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP001DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP002DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP003DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP004DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP005DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP006DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP007DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP008DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP009DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP010DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP011DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP012DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP013DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP014DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP015DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP016DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP017DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP018DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP019DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP020DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP021DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP022DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP023DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP024DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP025DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP026DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP027DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP028DerivativeNorm2558
  · simpa only [batchC02700MinusSignedMidpointValue2558, batchC02700MinusSignedMidpointError2558]
      using
      batchC02700MinusMidpointP029DerivativeNorm2558

noncomputable def batchC02700MinusSignedMidpointSum2558 : ℂ := ⟨(((-(((163416 * 10^40
        + 9351069749249456478441359019881974994289) * 10^40
        + 6643733738183665550903454171661714674079) * 10^40
        + 9254492069327022867540815959113942880357)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216)),
    (((-(((2828 * 10^40
        + 2607062440049205489498039068143279304113) * 10^40
        + 1659698053926523618046584638310875771935) * 10^40
        + 1828569785497861730500920835476385007059)) : ℝ) /
        (((21661481 * 10^40
        + 9853188660904563608136178414330971646513) * 10^40
        + 7356699351937172355172896723145017999980) * 10^40
        + 47688590453885868835635965404913860608))⟩

noncomputable def batchC02700MinusSignedMidpointUpper2558 : ℝ := ((377443 : ℝ) /
        100000000)

theorem batchC02700MinusSignedMidpointSum_eq2558 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02700MinusSignedMidpointValue2558 i) =
      batchC02700MinusSignedMidpointSum2558 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
        batchC02700MinusSignedMidpointValue2558,
      batchC02700MinusSignedMidpointSum2558, embedPair2542,
          batchC02700MinusMidpointP000Rounded2558,
      batchC02700MinusMidpointP001Rounded2558,
      batchC02700MinusMidpointP002Rounded2558,
      batchC02700MinusMidpointP003Rounded2558,
      batchC02700MinusMidpointP004Rounded2558,
      batchC02700MinusMidpointP005Rounded2558,
      batchC02700MinusMidpointP006Rounded2558,
      batchC02700MinusMidpointP007Rounded2558,
      batchC02700MinusMidpointP008Rounded2558,
      batchC02700MinusMidpointP009Rounded2558,
      batchC02700MinusMidpointP010Rounded2558,
      batchC02700MinusMidpointP011Rounded2558,
      batchC02700MinusMidpointP012Rounded2558,
      batchC02700MinusMidpointP013Rounded2558,
      batchC02700MinusMidpointP014Rounded2558,
      batchC02700MinusMidpointP015Rounded2558,
      batchC02700MinusMidpointP016Rounded2558,
      batchC02700MinusMidpointP017Rounded2558,
      batchC02700MinusMidpointP018Rounded2558,
      batchC02700MinusMidpointP019Rounded2558,
      batchC02700MinusMidpointP020Rounded2558,
      batchC02700MinusMidpointP021Rounded2558,
      batchC02700MinusMidpointP022Rounded2558,
      batchC02700MinusMidpointP023Rounded2558,
      batchC02700MinusMidpointP024Rounded2558,
      batchC02700MinusMidpointP025Rounded2558,
      batchC02700MinusMidpointP026Rounded2558,
      batchC02700MinusMidpointP027Rounded2558,
      batchC02700MinusMidpointP028Rounded2558,
      batchC02700MinusMidpointP029Rounded2558, Complex.mul_re, Complex.mul_im]

theorem batchC02700MinusSignedMidpointSum_norm2558 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02700MinusSignedMidpointValue2558 i‖ ≤
        ((377433 : ℝ) /
        100000000) := by
  rw [batchC02700MinusSignedMidpointSum_eq2558]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchC02700MinusSignedMidpointSum2558]

theorem batchC02700MinusSignedMidpointCharge2558 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchC02700MinusSignedMidpointError2558 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
      batchC02700MinusSignedMidpointError2558,
      batchC02700MinusMidpointP000Radius2558,
      batchC02700MinusMidpointP001Radius2558,
      batchC02700MinusMidpointP002Radius2558,
      batchC02700MinusMidpointP003Radius2558,
      batchC02700MinusMidpointP004Radius2558,
      batchC02700MinusMidpointP005Radius2558,
      batchC02700MinusMidpointP006Radius2558,
      batchC02700MinusMidpointP007Radius2558,
      batchC02700MinusMidpointP008Radius2558,
      batchC02700MinusMidpointP009Radius2558,
      batchC02700MinusMidpointP010Radius2558,
      batchC02700MinusMidpointP011Radius2558,
      batchC02700MinusMidpointP012Radius2558,
      batchC02700MinusMidpointP013Radius2558,
      batchC02700MinusMidpointP014Radius2558,
      batchC02700MinusMidpointP015Radius2558,
      batchC02700MinusMidpointP016Radius2558,
      batchC02700MinusMidpointP017Radius2558,
      batchC02700MinusMidpointP018Radius2558,
      batchC02700MinusMidpointP019Radius2558,
      batchC02700MinusMidpointP020Radius2558,
      batchC02700MinusMidpointP021Radius2558,
      batchC02700MinusMidpointP022Radius2558,
      batchC02700MinusMidpointP023Radius2558,
      batchC02700MinusMidpointP024Radius2558,
      batchC02700MinusMidpointP025Radius2558,
      batchC02700MinusMidpointP026Radius2558,
      batchC02700MinusMidpointP027Radius2558,
      batchC02700MinusMidpointP028Radius2558,
      batchC02700MinusMidpointP029Radius2558]

theorem batchC02700MinusSignedMidpointUpper_le2558 :
    signedJetUpper2539 2 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchC02700MinusMidpointPosition2558 ≤
          batchC02700MinusSignedMidpointUpper2558 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02700MinusMidpointPosition2558‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02700MinusSignedMidpointValue2558 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchC02700MinusSignedMidpointError2558 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (batchC02700MinusSignedMidpointExpError2558 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02700MinusMidpointPosition2558‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchC02700MinusSignedMidpointUnitNorm2558 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02700MinusMidpointPosition2558‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchC02700MinusSignedMidpointUpper2558
  linarith [batchC02700MinusSignedMidpointSum_norm2558, batchC02700MinusSignedMidpointCharge2558]

theorem batchC02700MinusPhysicalSecond2558 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        batchC02700MinusMidpointPosition2558‖ ≤
      batchC02700MinusSignedMidpointUpper2558 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchC02700MinusMidpointPosition2558
  exact h.trans batchC02700MinusSignedMidpointUpper_le2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02700MinusSignedMidpointExpError2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusSignedMidpointSum_eq2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusSignedMidpointCharge2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusSignedMidpointUpper_le2558
#print axioms ConnesWeilRH.Dev.batchC02700MinusPhysicalSecond2558
