import ConnesWeilRH.Dev.C1RouteABatchC02704MinusMidpoint2654

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem batchC02704MinusMidpoint_triangle2654 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def batchC02704MinusMidpointP000Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP000Radius2654 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02704MinusMidpointP000RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP000Factor2654
        batchC02704MinusMidpointP000Center2654) =
        batchC02704MinusMidpointP000Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP000RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP000Rounded2654‖ ≤
          batchC02704MinusMidpointP000Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP000Factor2654
      batchC02704MinusMidpointP000Center2654)
  rw [batchC02704MinusMidpointP000RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP000Factor2654 * embedPair2542
        batchC02704MinusMidpointP000Center2654)
    (embedPair2542 batchC02704MinusMidpointP000Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP000DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP000Factor2654,
      batchC02704MinusMidpointP000Error2654, rounding2542,
      batchC02704MinusMidpointP000Radius2654]

theorem batchC02704MinusMidpointP000DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP000Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP000RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP000Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP000Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP000Rounded2654]

def batchC02704MinusMidpointP001Rounded2654 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP001Radius2654 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704MinusMidpointP001RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP001Factor2654
        batchC02704MinusMidpointP001Center2654) =
        batchC02704MinusMidpointP001Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP001RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP001Rounded2654‖ ≤
          batchC02704MinusMidpointP001Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP001Factor2654
      batchC02704MinusMidpointP001Center2654)
  rw [batchC02704MinusMidpointP001RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP001Factor2654 * embedPair2542
        batchC02704MinusMidpointP001Center2654)
    (embedPair2542 batchC02704MinusMidpointP001Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP001DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP001Factor2654,
      batchC02704MinusMidpointP001Error2654, rounding2542,
      batchC02704MinusMidpointP001Radius2654]

theorem batchC02704MinusMidpointP001DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP001Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP001RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP001Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP001Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP001Rounded2654]

def batchC02704MinusMidpointP002Rounded2654 : RatPair2542 :=
  (((10209901 : ℚ) /
        316912650057057350374175801344),
    (((-18754979) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02704MinusMidpointP002Radius2654 : ℝ := ((1099511713715 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02704MinusMidpointP002RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP002Factor2654
        batchC02704MinusMidpointP002Center2654) =
        batchC02704MinusMidpointP002Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP002RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP002Rounded2654‖ ≤
          batchC02704MinusMidpointP002Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP002Factor2654
      batchC02704MinusMidpointP002Center2654)
  rw [batchC02704MinusMidpointP002RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP002Factor2654 * embedPair2542
        batchC02704MinusMidpointP002Center2654)
    (embedPair2542 batchC02704MinusMidpointP002Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP002DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP002Factor2654,
      batchC02704MinusMidpointP002Error2654, rounding2542,
      batchC02704MinusMidpointP002Radius2654]

theorem batchC02704MinusMidpointP002DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP002Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP002RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP002Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP002Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP002Rounded2654]

def batchC02704MinusMidpointP003Rounded2654 : RatPair2542 :=
  (((327659012414777 : ℚ) /
        1267650600228229401496703205376),
    ((87433454695419 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC02704MinusMidpointP003Radius2654 : ℝ := ((4034059430585 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704MinusMidpointP003RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP003Factor2654
        batchC02704MinusMidpointP003Center2654) =
        batchC02704MinusMidpointP003Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP003RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP003Rounded2654‖ ≤
          batchC02704MinusMidpointP003Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP003Factor2654
      batchC02704MinusMidpointP003Center2654)
  rw [batchC02704MinusMidpointP003RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP003Factor2654 * embedPair2542
        batchC02704MinusMidpointP003Center2654)
    (embedPair2542 batchC02704MinusMidpointP003Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP003DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP003Factor2654,
      batchC02704MinusMidpointP003Error2654, rounding2542,
      batchC02704MinusMidpointP003Radius2654]

theorem batchC02704MinusMidpointP003DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP003Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP003RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP003Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP003Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP003Rounded2654]

def batchC02704MinusMidpointP004Rounded2654 : RatPair2542 :=
  (((111724427130535523 : ℚ) /
        1267650600228229401496703205376),
    (((-121035206151632265) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02704MinusMidpointP004Radius2654 : ℝ := ((722018806761443 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704MinusMidpointP004RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP004Factor2654
        batchC02704MinusMidpointP004Center2654) =
        batchC02704MinusMidpointP004Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP004RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP004Rounded2654‖ ≤
          batchC02704MinusMidpointP004Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP004Factor2654
      batchC02704MinusMidpointP004Center2654)
  rw [batchC02704MinusMidpointP004RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP004Factor2654 * embedPair2542
        batchC02704MinusMidpointP004Center2654)
    (embedPair2542 batchC02704MinusMidpointP004Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP004DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP004Factor2654,
      batchC02704MinusMidpointP004Error2654, rounding2542,
      batchC02704MinusMidpointP004Radius2654]

theorem batchC02704MinusMidpointP004DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP004Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP004RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP004Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP004Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP004Rounded2654]

def batchC02704MinusMidpointP005Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP005Radius2654 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02704MinusMidpointP005RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP005Factor2654
        batchC02704MinusMidpointP005Center2654) =
        batchC02704MinusMidpointP005Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP005RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP005Rounded2654‖ ≤
          batchC02704MinusMidpointP005Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP005Factor2654
      batchC02704MinusMidpointP005Center2654)
  rw [batchC02704MinusMidpointP005RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP005Factor2654 * embedPair2542
        batchC02704MinusMidpointP005Center2654)
    (embedPair2542 batchC02704MinusMidpointP005Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP005DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP005Factor2654,
      batchC02704MinusMidpointP005Error2654, rounding2542,
      batchC02704MinusMidpointP005Radius2654]

theorem batchC02704MinusMidpointP005DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP005Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP005RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP005Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP005Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP005Rounded2654]

def batchC02704MinusMidpointP006Rounded2654 : RatPair2542 :=
  (((31 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP006Radius2654 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704MinusMidpointP006RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP006Factor2654
        batchC02704MinusMidpointP006Center2654) =
        batchC02704MinusMidpointP006Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP006RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP006Rounded2654‖ ≤
          batchC02704MinusMidpointP006Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP006Factor2654
      batchC02704MinusMidpointP006Center2654)
  rw [batchC02704MinusMidpointP006RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP006Factor2654 * embedPair2542
        batchC02704MinusMidpointP006Center2654)
    (embedPair2542 batchC02704MinusMidpointP006Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP006DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP006Factor2654,
      batchC02704MinusMidpointP006Error2654, rounding2542,
      batchC02704MinusMidpointP006Radius2654]

theorem batchC02704MinusMidpointP006DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP006Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP006RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP006Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP006Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP006Rounded2654]

def batchC02704MinusMidpointP007Rounded2654 : RatPair2542 :=
  (((37491910008163 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP007Radius2654 : ℝ := ((1102103598563 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02704MinusMidpointP007RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP007Factor2654
        batchC02704MinusMidpointP007Center2654) =
        batchC02704MinusMidpointP007Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP007RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP007Rounded2654‖ ≤
          batchC02704MinusMidpointP007Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP007Factor2654
      batchC02704MinusMidpointP007Center2654)
  rw [batchC02704MinusMidpointP007RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP007Factor2654 * embedPair2542
        batchC02704MinusMidpointP007Center2654)
    (embedPair2542 batchC02704MinusMidpointP007Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP007DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP007Factor2654,
      batchC02704MinusMidpointP007Error2654, rounding2542,
      batchC02704MinusMidpointP007Radius2654]

theorem batchC02704MinusMidpointP007DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP007Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP007RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP007Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP007Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP007Rounded2654]

def batchC02704MinusMidpointP008Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP008Radius2654 : ℝ := ((1099513497845 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02704MinusMidpointP008RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP008Factor2654
        batchC02704MinusMidpointP008Center2654) =
        batchC02704MinusMidpointP008Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP008RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP008Rounded2654‖ ≤
          batchC02704MinusMidpointP008Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP008Factor2654
      batchC02704MinusMidpointP008Center2654)
  rw [batchC02704MinusMidpointP008RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP008Factor2654 * embedPair2542
        batchC02704MinusMidpointP008Center2654)
    (embedPair2542 batchC02704MinusMidpointP008Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP008DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP008Factor2654,
      batchC02704MinusMidpointP008Error2654, rounding2542,
      batchC02704MinusMidpointP008Radius2654]

theorem batchC02704MinusMidpointP008DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP008Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP008RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP008Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP008Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP008Rounded2654]

def batchC02704MinusMidpointP009Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP009Radius2654 : ℝ := ((2199026995727 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704MinusMidpointP009RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP009Factor2654
        batchC02704MinusMidpointP009Center2654) =
        batchC02704MinusMidpointP009Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP009RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP009Rounded2654‖ ≤
          batchC02704MinusMidpointP009Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP009Factor2654
      batchC02704MinusMidpointP009Center2654)
  rw [batchC02704MinusMidpointP009RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP009Factor2654 * embedPair2542
        batchC02704MinusMidpointP009Center2654)
    (embedPair2542 batchC02704MinusMidpointP009Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP009DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP009Factor2654,
      batchC02704MinusMidpointP009Error2654, rounding2542,
      batchC02704MinusMidpointP009Radius2654]

theorem batchC02704MinusMidpointP009DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP009Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP009RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP009Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP009Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP009Rounded2654]

def batchC02704MinusMidpointP010Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP010Radius2654 : ℝ := ((549756748937 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02704MinusMidpointP010RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP010Factor2654
        batchC02704MinusMidpointP010Center2654) =
        batchC02704MinusMidpointP010Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP010RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP010Rounded2654‖ ≤
          batchC02704MinusMidpointP010Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP010Factor2654
      batchC02704MinusMidpointP010Center2654)
  rw [batchC02704MinusMidpointP010RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP010Factor2654 * embedPair2542
        batchC02704MinusMidpointP010Center2654)
    (embedPair2542 batchC02704MinusMidpointP010Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP010DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP010Factor2654,
      batchC02704MinusMidpointP010Error2654, rounding2542,
      batchC02704MinusMidpointP010Radius2654]

theorem batchC02704MinusMidpointP010DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP010Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP010RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP010Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP010Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP010Rounded2654]

def batchC02704MinusMidpointP011Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP011Radius2654 : ℝ := ((1099513497881 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02704MinusMidpointP011RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP011Factor2654
        batchC02704MinusMidpointP011Center2654) =
        batchC02704MinusMidpointP011Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP011RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP011Rounded2654‖ ≤
          batchC02704MinusMidpointP011Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP011Factor2654
      batchC02704MinusMidpointP011Center2654)
  rw [batchC02704MinusMidpointP011RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP011Factor2654 * embedPair2542
        batchC02704MinusMidpointP011Center2654)
    (embedPair2542 batchC02704MinusMidpointP011Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP011DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP011Factor2654,
      batchC02704MinusMidpointP011Error2654, rounding2542,
      batchC02704MinusMidpointP011Radius2654]

theorem batchC02704MinusMidpointP011DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP011Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP011RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP011Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP011Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP011Rounded2654]

def batchC02704MinusMidpointP012Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP012Radius2654 : ℝ := ((2199026995777 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704MinusMidpointP012RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP012Factor2654
        batchC02704MinusMidpointP012Center2654) =
        batchC02704MinusMidpointP012Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP012RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP012Rounded2654‖ ≤
          batchC02704MinusMidpointP012Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP012Factor2654
      batchC02704MinusMidpointP012Center2654)
  rw [batchC02704MinusMidpointP012RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP012Factor2654 * embedPair2542
        batchC02704MinusMidpointP012Center2654)
    (embedPair2542 batchC02704MinusMidpointP012Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP012DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP012Factor2654,
      batchC02704MinusMidpointP012Error2654, rounding2542,
      batchC02704MinusMidpointP012Radius2654]

theorem batchC02704MinusMidpointP012DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP012Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP012RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP012Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP012Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP012Rounded2654]

def batchC02704MinusMidpointP013Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP013Radius2654 : ℝ := ((2199026995791 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704MinusMidpointP013RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP013Factor2654
        batchC02704MinusMidpointP013Center2654) =
        batchC02704MinusMidpointP013Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP013RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP013Rounded2654‖ ≤
          batchC02704MinusMidpointP013Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP013Factor2654
      batchC02704MinusMidpointP013Center2654)
  rw [batchC02704MinusMidpointP013RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP013Factor2654 * embedPair2542
        batchC02704MinusMidpointP013Center2654)
    (embedPair2542 batchC02704MinusMidpointP013Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP013DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP013Factor2654,
      batchC02704MinusMidpointP013Error2654, rounding2542,
      batchC02704MinusMidpointP013Radius2654]

theorem batchC02704MinusMidpointP013DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP013Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP013RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP013Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP013Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP013Rounded2654]

def batchC02704MinusMidpointP014Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP014Radius2654 : ℝ := ((2199026995815 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704MinusMidpointP014RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP014Factor2654
        batchC02704MinusMidpointP014Center2654) =
        batchC02704MinusMidpointP014Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP014RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP014Rounded2654‖ ≤
          batchC02704MinusMidpointP014Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP014Factor2654
      batchC02704MinusMidpointP014Center2654)
  rw [batchC02704MinusMidpointP014RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP014Factor2654 * embedPair2542
        batchC02704MinusMidpointP014Center2654)
    (embedPair2542 batchC02704MinusMidpointP014Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP014DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP014Factor2654,
      batchC02704MinusMidpointP014Error2654, rounding2542,
      batchC02704MinusMidpointP014Radius2654]

theorem batchC02704MinusMidpointP014DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP014Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP014RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP014Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP014Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP014Rounded2654]

def batchC02704MinusMidpointP015Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP015Radius2654 : ℝ := ((2199026995833 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704MinusMidpointP015RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP015Factor2654
        batchC02704MinusMidpointP015Center2654) =
        batchC02704MinusMidpointP015Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP015RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP015Rounded2654‖ ≤
          batchC02704MinusMidpointP015Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP015Factor2654
      batchC02704MinusMidpointP015Center2654)
  rw [batchC02704MinusMidpointP015RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP015Factor2654 * embedPair2542
        batchC02704MinusMidpointP015Center2654)
    (embedPair2542 batchC02704MinusMidpointP015Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP015DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP015Factor2654,
      batchC02704MinusMidpointP015Error2654, rounding2542,
      batchC02704MinusMidpointP015Radius2654]

theorem batchC02704MinusMidpointP015DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP015Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP015RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP015Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP015Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP015Rounded2654]

def batchC02704MinusMidpointP016Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP016Radius2654 : ℝ := ((1099513497923 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02704MinusMidpointP016RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP016Factor2654
        batchC02704MinusMidpointP016Center2654) =
        batchC02704MinusMidpointP016Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP016RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP016Rounded2654‖ ≤
          batchC02704MinusMidpointP016Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP016Factor2654
      batchC02704MinusMidpointP016Center2654)
  rw [batchC02704MinusMidpointP016RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP016Factor2654 * embedPair2542
        batchC02704MinusMidpointP016Center2654)
    (embedPair2542 batchC02704MinusMidpointP016Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP016DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP016Factor2654,
      batchC02704MinusMidpointP016Error2654, rounding2542,
      batchC02704MinusMidpointP016Radius2654]

theorem batchC02704MinusMidpointP016DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP016Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP016RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP016Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP016Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP016Rounded2654]

def batchC02704MinusMidpointP017Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP017Radius2654 : ℝ := ((2199026995871 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704MinusMidpointP017RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP017Factor2654
        batchC02704MinusMidpointP017Center2654) =
        batchC02704MinusMidpointP017Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP017RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP017Rounded2654‖ ≤
          batchC02704MinusMidpointP017Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP017Factor2654
      batchC02704MinusMidpointP017Center2654)
  rw [batchC02704MinusMidpointP017RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP017Factor2654 * embedPair2542
        batchC02704MinusMidpointP017Center2654)
    (embedPair2542 batchC02704MinusMidpointP017Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP017DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP017Factor2654,
      batchC02704MinusMidpointP017Error2654, rounding2542,
      batchC02704MinusMidpointP017Radius2654]

theorem batchC02704MinusMidpointP017DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP017Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP017RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP017Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP017Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP017Rounded2654]

def batchC02704MinusMidpointP018Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP018Radius2654 : ℝ := ((2199026995881 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704MinusMidpointP018RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP018Factor2654
        batchC02704MinusMidpointP018Center2654) =
        batchC02704MinusMidpointP018Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP018RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP018Rounded2654‖ ≤
          batchC02704MinusMidpointP018Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP018Factor2654
      batchC02704MinusMidpointP018Center2654)
  rw [batchC02704MinusMidpointP018RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP018Factor2654 * embedPair2542
        batchC02704MinusMidpointP018Center2654)
    (embedPair2542 batchC02704MinusMidpointP018Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP018DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP018Factor2654,
      batchC02704MinusMidpointP018Error2654, rounding2542,
      batchC02704MinusMidpointP018Radius2654]

theorem batchC02704MinusMidpointP018DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP018Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP018RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP018Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP018Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP018Rounded2654]

def batchC02704MinusMidpointP019Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP019Radius2654 : ℝ := ((1099513497949 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02704MinusMidpointP019RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP019Factor2654
        batchC02704MinusMidpointP019Center2654) =
        batchC02704MinusMidpointP019Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP019RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP019Rounded2654‖ ≤
          batchC02704MinusMidpointP019Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP019Factor2654
      batchC02704MinusMidpointP019Center2654)
  rw [batchC02704MinusMidpointP019RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP019Factor2654 * embedPair2542
        batchC02704MinusMidpointP019Center2654)
    (embedPair2542 batchC02704MinusMidpointP019Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP019DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP019Factor2654,
      batchC02704MinusMidpointP019Error2654, rounding2542,
      batchC02704MinusMidpointP019Radius2654]

theorem batchC02704MinusMidpointP019DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP019Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP019RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP019Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP019Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP019Rounded2654]

def batchC02704MinusMidpointP020Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP020Radius2654 : ℝ := ((549756748979 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02704MinusMidpointP020RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP020Factor2654
        batchC02704MinusMidpointP020Center2654) =
        batchC02704MinusMidpointP020Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP020RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP020Rounded2654‖ ≤
          batchC02704MinusMidpointP020Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP020Factor2654
      batchC02704MinusMidpointP020Center2654)
  rw [batchC02704MinusMidpointP020RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP020Factor2654 * embedPair2542
        batchC02704MinusMidpointP020Center2654)
    (embedPair2542 batchC02704MinusMidpointP020Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP020DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP020Factor2654,
      batchC02704MinusMidpointP020Error2654, rounding2542,
      batchC02704MinusMidpointP020Radius2654]

theorem batchC02704MinusMidpointP020DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP020Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP020RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP020Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP020Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP020Rounded2654]

def batchC02704MinusMidpointP021Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP021Radius2654 : ℝ := ((549756748983 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02704MinusMidpointP021RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP021Factor2654
        batchC02704MinusMidpointP021Center2654) =
        batchC02704MinusMidpointP021Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP021RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP021Rounded2654‖ ≤
          batchC02704MinusMidpointP021Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP021Factor2654
      batchC02704MinusMidpointP021Center2654)
  rw [batchC02704MinusMidpointP021RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP021Factor2654 * embedPair2542
        batchC02704MinusMidpointP021Center2654)
    (embedPair2542 batchC02704MinusMidpointP021Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP021DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP021Factor2654,
      batchC02704MinusMidpointP021Error2654, rounding2542,
      batchC02704MinusMidpointP021Radius2654]

theorem batchC02704MinusMidpointP021DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP021Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP021RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP021Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP021Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP021Rounded2654]

def batchC02704MinusMidpointP022Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP022Radius2654 : ℝ := ((549756748985 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02704MinusMidpointP022RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP022Factor2654
        batchC02704MinusMidpointP022Center2654) =
        batchC02704MinusMidpointP022Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP022RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP022Rounded2654‖ ≤
          batchC02704MinusMidpointP022Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP022Factor2654
      batchC02704MinusMidpointP022Center2654)
  rw [batchC02704MinusMidpointP022RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP022Factor2654 * embedPair2542
        batchC02704MinusMidpointP022Center2654)
    (embedPair2542 batchC02704MinusMidpointP022Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP022DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP022Factor2654,
      batchC02704MinusMidpointP022Error2654, rounding2542,
      batchC02704MinusMidpointP022Radius2654]

theorem batchC02704MinusMidpointP022DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP022Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP022RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP022Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP022Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP022Rounded2654]

def batchC02704MinusMidpointP023Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP023Radius2654 : ℝ := ((1099513497981 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02704MinusMidpointP023RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP023Factor2654
        batchC02704MinusMidpointP023Center2654) =
        batchC02704MinusMidpointP023Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP023RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP023Rounded2654‖ ≤
          batchC02704MinusMidpointP023Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP023Factor2654
      batchC02704MinusMidpointP023Center2654)
  rw [batchC02704MinusMidpointP023RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP023Factor2654 * embedPair2542
        batchC02704MinusMidpointP023Center2654)
    (embedPair2542 batchC02704MinusMidpointP023Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP023DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP023Factor2654,
      batchC02704MinusMidpointP023Error2654, rounding2542,
      batchC02704MinusMidpointP023Radius2654]

theorem batchC02704MinusMidpointP023DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP023Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP023RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP023Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP023Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP023Rounded2654]

def batchC02704MinusMidpointP024Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP024Radius2654 : ℝ := ((2199026995973 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704MinusMidpointP024RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP024Factor2654
        batchC02704MinusMidpointP024Center2654) =
        batchC02704MinusMidpointP024Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP024RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP024Rounded2654‖ ≤
          batchC02704MinusMidpointP024Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP024Factor2654
      batchC02704MinusMidpointP024Center2654)
  rw [batchC02704MinusMidpointP024RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP024Factor2654 * embedPair2542
        batchC02704MinusMidpointP024Center2654)
    (embedPair2542 batchC02704MinusMidpointP024Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP024DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP024Factor2654,
      batchC02704MinusMidpointP024Error2654, rounding2542,
      batchC02704MinusMidpointP024Radius2654]

theorem batchC02704MinusMidpointP024DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP024Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP024RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP024Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP024Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP024Rounded2654]

def batchC02704MinusMidpointP025Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP025Radius2654 : ℝ := ((1099513497993 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02704MinusMidpointP025RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP025Factor2654
        batchC02704MinusMidpointP025Center2654) =
        batchC02704MinusMidpointP025Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP025RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP025Rounded2654‖ ≤
          batchC02704MinusMidpointP025Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP025Factor2654
      batchC02704MinusMidpointP025Center2654)
  rw [batchC02704MinusMidpointP025RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP025Factor2654 * embedPair2542
        batchC02704MinusMidpointP025Center2654)
    (embedPair2542 batchC02704MinusMidpointP025Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP025DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP025Factor2654,
      batchC02704MinusMidpointP025Error2654, rounding2542,
      batchC02704MinusMidpointP025Radius2654]

theorem batchC02704MinusMidpointP025DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP025Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP025RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP025Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP025Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP025Rounded2654]

def batchC02704MinusMidpointP026Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP026Radius2654 : ℝ := ((68719593625 : ℝ) /
        (4 * 10^40
        + 3556142965880123323311949751266331066368))

theorem batchC02704MinusMidpointP026RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP026Factor2654
        batchC02704MinusMidpointP026Center2654) =
        batchC02704MinusMidpointP026Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP026RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP026Rounded2654‖ ≤
          batchC02704MinusMidpointP026Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP026Factor2654
      batchC02704MinusMidpointP026Center2654)
  rw [batchC02704MinusMidpointP026RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP026Factor2654 * embedPair2542
        batchC02704MinusMidpointP026Center2654)
    (embedPair2542 batchC02704MinusMidpointP026Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP026DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP026Factor2654,
      batchC02704MinusMidpointP026Error2654, rounding2542,
      batchC02704MinusMidpointP026Radius2654]

theorem batchC02704MinusMidpointP026DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP026Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP026RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP026Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP026Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP026Rounded2654]

def batchC02704MinusMidpointP027Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP027Radius2654 : ℝ := ((2199026996019 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704MinusMidpointP027RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP027Factor2654
        batchC02704MinusMidpointP027Center2654) =
        batchC02704MinusMidpointP027Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP027RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP027Rounded2654‖ ≤
          batchC02704MinusMidpointP027Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP027Factor2654
      batchC02704MinusMidpointP027Center2654)
  rw [batchC02704MinusMidpointP027RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP027Factor2654 * embedPair2542
        batchC02704MinusMidpointP027Center2654)
    (embedPair2542 batchC02704MinusMidpointP027Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP027DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP027Factor2654,
      batchC02704MinusMidpointP027Error2654, rounding2542,
      batchC02704MinusMidpointP027Radius2654]

theorem batchC02704MinusMidpointP027DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP027Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP027RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP027Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP027Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP027Rounded2654]

def batchC02704MinusMidpointP028Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP028Radius2654 : ℝ := ((2199026996027 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704MinusMidpointP028RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP028Factor2654
        batchC02704MinusMidpointP028Center2654) =
        batchC02704MinusMidpointP028Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP028RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP028Rounded2654‖ ≤
          batchC02704MinusMidpointP028Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP028Factor2654
      batchC02704MinusMidpointP028Center2654)
  rw [batchC02704MinusMidpointP028RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP028Factor2654 * embedPair2542
        batchC02704MinusMidpointP028Center2654)
    (embedPair2542 batchC02704MinusMidpointP028Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP028DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP028Factor2654,
      batchC02704MinusMidpointP028Error2654, rounding2542,
      batchC02704MinusMidpointP028Radius2654]

theorem batchC02704MinusMidpointP028DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP028Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP028RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP028Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP028Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP028Rounded2654]

def batchC02704MinusMidpointP029Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704MinusMidpointP029Radius2654 : ℝ := ((1099513498019 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02704MinusMidpointP029RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704MinusMidpointP029Factor2654
        batchC02704MinusMidpointP029Center2654) =
        batchC02704MinusMidpointP029Rounded2654 := by
  cbv

theorem batchC02704MinusMidpointP029RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02704MinusMidpointPosition2654 -
      embedPair2542 batchC02704MinusMidpointP029Rounded2654‖ ≤
          batchC02704MinusMidpointP029Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704MinusMidpointP029Factor2654
      batchC02704MinusMidpointP029Center2654)
  rw [batchC02704MinusMidpointP029RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP029Factor2654 * embedPair2542
        batchC02704MinusMidpointP029Center2654)
    (embedPair2542 batchC02704MinusMidpointP029Rounded2654)).trans (add_le_add
        batchC02704MinusMidpointP029DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704MinusMidpointP029Factor2654,
      batchC02704MinusMidpointP029Error2654, rounding2542,
      batchC02704MinusMidpointP029Radius2654]

theorem batchC02704MinusMidpointP029DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02704MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02704MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02704MinusMidpointPosition2654)
    (embedPair2542 batchC02704MinusMidpointP029Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704MinusMidpointP029RoundedError2654
      (embedPair_magnitude2542
      batchC02704MinusMidpointP029Rounded2654))
  apply h'.trans
  norm_num [batchC02704MinusMidpointP029Radius2654, pairMagnitude2542,
      batchC02704MinusMidpointP029Rounded2654]

noncomputable def batchC02704MinusSignedMidpointValue2654 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchC02704MinusMidpointP000Rounded2654
  | 1 => embedPair2542 batchC02704MinusMidpointP001Rounded2654
  | 2 => embedPair2542 batchC02704MinusMidpointP002Rounded2654
  | 3 => embedPair2542 batchC02704MinusMidpointP003Rounded2654
  | 4 => embedPair2542 batchC02704MinusMidpointP004Rounded2654
  | 5 => embedPair2542 batchC02704MinusMidpointP005Rounded2654
  | 6 => embedPair2542 batchC02704MinusMidpointP006Rounded2654
  | 7 => embedPair2542 batchC02704MinusMidpointP007Rounded2654
  | 8 => embedPair2542 batchC02704MinusMidpointP008Rounded2654
  | 9 => embedPair2542 batchC02704MinusMidpointP009Rounded2654
  | 10 => embedPair2542 batchC02704MinusMidpointP010Rounded2654
  | 11 => embedPair2542 batchC02704MinusMidpointP011Rounded2654
  | 12 => embedPair2542 batchC02704MinusMidpointP012Rounded2654
  | 13 => embedPair2542 batchC02704MinusMidpointP013Rounded2654
  | 14 => embedPair2542 batchC02704MinusMidpointP014Rounded2654
  | 15 => embedPair2542 batchC02704MinusMidpointP015Rounded2654
  | 16 => embedPair2542 batchC02704MinusMidpointP016Rounded2654
  | 17 => embedPair2542 batchC02704MinusMidpointP017Rounded2654
  | 18 => embedPair2542 batchC02704MinusMidpointP018Rounded2654
  | 19 => embedPair2542 batchC02704MinusMidpointP019Rounded2654
  | 20 => embedPair2542 batchC02704MinusMidpointP020Rounded2654
  | 21 => embedPair2542 batchC02704MinusMidpointP021Rounded2654
  | 22 => embedPair2542 batchC02704MinusMidpointP022Rounded2654
  | 23 => embedPair2542 batchC02704MinusMidpointP023Rounded2654
  | 24 => embedPair2542 batchC02704MinusMidpointP024Rounded2654
  | 25 => embedPair2542 batchC02704MinusMidpointP025Rounded2654
  | 26 => embedPair2542 batchC02704MinusMidpointP026Rounded2654
  | 27 => embedPair2542 batchC02704MinusMidpointP027Rounded2654
  | 28 => embedPair2542 batchC02704MinusMidpointP028Rounded2654
  | 29 => embedPair2542 batchC02704MinusMidpointP029Rounded2654
  | _ => 0

noncomputable def batchC02704MinusSignedMidpointError2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02704MinusMidpointP000Radius2654
  | 1 => batchC02704MinusMidpointP001Radius2654
  | 2 => batchC02704MinusMidpointP002Radius2654
  | 3 => batchC02704MinusMidpointP003Radius2654
  | 4 => batchC02704MinusMidpointP004Radius2654
  | 5 => batchC02704MinusMidpointP005Radius2654
  | 6 => batchC02704MinusMidpointP006Radius2654
  | 7 => batchC02704MinusMidpointP007Radius2654
  | 8 => batchC02704MinusMidpointP008Radius2654
  | 9 => batchC02704MinusMidpointP009Radius2654
  | 10 => batchC02704MinusMidpointP010Radius2654
  | 11 => batchC02704MinusMidpointP011Radius2654
  | 12 => batchC02704MinusMidpointP012Radius2654
  | 13 => batchC02704MinusMidpointP013Radius2654
  | 14 => batchC02704MinusMidpointP014Radius2654
  | 15 => batchC02704MinusMidpointP015Radius2654
  | 16 => batchC02704MinusMidpointP016Radius2654
  | 17 => batchC02704MinusMidpointP017Radius2654
  | 18 => batchC02704MinusMidpointP018Radius2654
  | 19 => batchC02704MinusMidpointP019Radius2654
  | 20 => batchC02704MinusMidpointP020Radius2654
  | 21 => batchC02704MinusMidpointP021Radius2654
  | 22 => batchC02704MinusMidpointP022Radius2654
  | 23 => batchC02704MinusMidpointP023Radius2654
  | 24 => batchC02704MinusMidpointP024Radius2654
  | 25 => batchC02704MinusMidpointP025Radius2654
  | 26 => batchC02704MinusMidpointP026Radius2654
  | 27 => batchC02704MinusMidpointP027Radius2654
  | 28 => batchC02704MinusMidpointP028Radius2654
  | 29 => batchC02704MinusMidpointP029Radius2654
  | _ => 0

theorem batchC02704MinusSignedMidpointExpError2654 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02704MinusMidpointPosition2654 -
        batchC02704MinusSignedMidpointValue2654 i‖ ≤ batchC02704MinusSignedMidpointError2654 i :=
            by
  fin_cases i
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP000RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP001RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP002RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP003RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP004RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP005RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP006RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP007RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP008RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP009RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP010RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP011RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP012RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP013RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP014RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP015RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP016RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP017RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP018RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP019RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP020RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP021RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP022RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP023RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP024RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP025RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP026RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP027RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP028RoundedError2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP029RoundedError2654

theorem batchC02704MinusSignedMidpointUnitNorm2654 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02704MinusMidpointPosition2654‖ ≤ 1
        := by
  fin_cases i
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP000DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP001DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP002DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP003DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP004DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP005DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP006DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP007DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP008DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP009DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP010DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP011DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP012DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP013DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP014DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP015DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP016DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP017DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP018DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP019DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP020DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP021DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP022DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP023DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP024DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP025DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP026DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP027DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP028DerivativeNorm2654
  · simpa only [batchC02704MinusSignedMidpointValue2654, batchC02704MinusSignedMidpointError2654]
      using
      batchC02704MinusMidpointP029DerivativeNorm2654

noncomputable def batchC02704MinusSignedMidpointSum2654 : ℂ := ⟨(((-(((156103 * 10^40
        + 7138773418056404913009258007533610993489) * 10^40
        + 7973115243563782851298673960017245812895) * 10^40
        + 4667687735212456663008545409618674856167)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216)),
    (((-(((2870 * 10^40
        + 3257981554350177157258672783388402028906) * 10^40
        + 1450810986837419919564848420493508437581) * 10^40
        + 9606237920203945953549023853564215290577)) : ℝ) /
        (((5415370 * 10^40
        + 4963297165226140902034044603582742911628) * 10^40
        + 4339174837984293088793224180786254499995) * 10^40
        + 11922147613471467208908991351228465152))⟩

noncomputable def batchC02704MinusSignedMidpointUpper2654 : ℝ := ((182107 : ℝ) /
        50000000)

theorem batchC02704MinusSignedMidpointSum_eq2654 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02704MinusSignedMidpointValue2654 i) =
      batchC02704MinusSignedMidpointSum2654 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
        batchC02704MinusSignedMidpointValue2654,
      batchC02704MinusSignedMidpointSum2654, embedPair2542,
          batchC02704MinusMidpointP000Rounded2654,
      batchC02704MinusMidpointP001Rounded2654,
      batchC02704MinusMidpointP002Rounded2654,
      batchC02704MinusMidpointP003Rounded2654,
      batchC02704MinusMidpointP004Rounded2654,
      batchC02704MinusMidpointP005Rounded2654,
      batchC02704MinusMidpointP006Rounded2654,
      batchC02704MinusMidpointP007Rounded2654,
      batchC02704MinusMidpointP008Rounded2654,
      batchC02704MinusMidpointP009Rounded2654,
      batchC02704MinusMidpointP010Rounded2654,
      batchC02704MinusMidpointP011Rounded2654,
      batchC02704MinusMidpointP012Rounded2654,
      batchC02704MinusMidpointP013Rounded2654,
      batchC02704MinusMidpointP014Rounded2654,
      batchC02704MinusMidpointP015Rounded2654,
      batchC02704MinusMidpointP016Rounded2654,
      batchC02704MinusMidpointP017Rounded2654,
      batchC02704MinusMidpointP018Rounded2654,
      batchC02704MinusMidpointP019Rounded2654,
      batchC02704MinusMidpointP020Rounded2654,
      batchC02704MinusMidpointP021Rounded2654,
      batchC02704MinusMidpointP022Rounded2654,
      batchC02704MinusMidpointP023Rounded2654,
      batchC02704MinusMidpointP024Rounded2654,
      batchC02704MinusMidpointP025Rounded2654,
      batchC02704MinusMidpointP026Rounded2654,
      batchC02704MinusMidpointP027Rounded2654,
      batchC02704MinusMidpointP028Rounded2654,
      batchC02704MinusMidpointP029Rounded2654, Complex.mul_re, Complex.mul_im]

theorem batchC02704MinusSignedMidpointSum_norm2654 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02704MinusSignedMidpointValue2654 i‖ ≤
        ((91051 : ℝ) /
        25000000) := by
  rw [batchC02704MinusSignedMidpointSum_eq2654]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchC02704MinusSignedMidpointSum2654]

theorem batchC02704MinusSignedMidpointCharge2654 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchC02704MinusSignedMidpointError2654 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
      batchC02704MinusSignedMidpointError2654,
      batchC02704MinusMidpointP000Radius2654,
      batchC02704MinusMidpointP001Radius2654,
      batchC02704MinusMidpointP002Radius2654,
      batchC02704MinusMidpointP003Radius2654,
      batchC02704MinusMidpointP004Radius2654,
      batchC02704MinusMidpointP005Radius2654,
      batchC02704MinusMidpointP006Radius2654,
      batchC02704MinusMidpointP007Radius2654,
      batchC02704MinusMidpointP008Radius2654,
      batchC02704MinusMidpointP009Radius2654,
      batchC02704MinusMidpointP010Radius2654,
      batchC02704MinusMidpointP011Radius2654,
      batchC02704MinusMidpointP012Radius2654,
      batchC02704MinusMidpointP013Radius2654,
      batchC02704MinusMidpointP014Radius2654,
      batchC02704MinusMidpointP015Radius2654,
      batchC02704MinusMidpointP016Radius2654,
      batchC02704MinusMidpointP017Radius2654,
      batchC02704MinusMidpointP018Radius2654,
      batchC02704MinusMidpointP019Radius2654,
      batchC02704MinusMidpointP020Radius2654,
      batchC02704MinusMidpointP021Radius2654,
      batchC02704MinusMidpointP022Radius2654,
      batchC02704MinusMidpointP023Radius2654,
      batchC02704MinusMidpointP024Radius2654,
      batchC02704MinusMidpointP025Radius2654,
      batchC02704MinusMidpointP026Radius2654,
      batchC02704MinusMidpointP027Radius2654,
      batchC02704MinusMidpointP028Radius2654,
      batchC02704MinusMidpointP029Radius2654]

theorem batchC02704MinusSignedMidpointUpper_le2654 :
    signedJetUpper2539 2 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchC02704MinusMidpointPosition2654 ≤
          batchC02704MinusSignedMidpointUpper2654 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02704MinusMidpointPosition2654‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02704MinusSignedMidpointValue2654 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchC02704MinusSignedMidpointError2654 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (batchC02704MinusSignedMidpointExpError2654 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02704MinusMidpointPosition2654‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchC02704MinusSignedMidpointUnitNorm2654 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02704MinusMidpointPosition2654‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchC02704MinusSignedMidpointUpper2654
  linarith [batchC02704MinusSignedMidpointSum_norm2654, batchC02704MinusSignedMidpointCharge2654]

theorem batchC02704MinusPhysicalSecond2654 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        batchC02704MinusMidpointPosition2654‖ ≤
      batchC02704MinusSignedMidpointUpper2654 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchC02704MinusMidpointPosition2654
  exact h.trans batchC02704MinusSignedMidpointUpper_le2654

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02704MinusSignedMidpointExpError2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusSignedMidpointSum_eq2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusSignedMidpointCharge2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusSignedMidpointUpper_le2654
#print axioms ConnesWeilRH.Dev.batchC02704MinusPhysicalSecond2654
