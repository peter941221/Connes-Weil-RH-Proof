import ConnesWeilRH.Dev.C1RouteABatchC05120MinusMidpoint2559

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem batchC05120MinusMidpoint_triangle2559 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def batchC05120MinusMidpointP000Rounded2559 : RatPair2542 :=
  ((((-5737111873938200909) : ℚ) /
        39614081257132168796771975168),
    ((4661857991838888347 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120MinusMidpointP000Radius2559 : ℝ := ((8674776290749969 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120MinusMidpointP000RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP000Factor2559
        batchC05120MinusMidpointP000Center2559) =
        batchC05120MinusMidpointP000Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP000RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP000Rounded2559‖ ≤
          batchC05120MinusMidpointP000Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP000Factor2559
      batchC05120MinusMidpointP000Center2559)
  rw [batchC05120MinusMidpointP000RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP000Factor2559 * embedPair2542
        batchC05120MinusMidpointP000Center2559)
    (embedPair2542 batchC05120MinusMidpointP000Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP000DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP000Factor2559,
      batchC05120MinusMidpointP000Error2559, rounding2542,
      batchC05120MinusMidpointP000Radius2559]

theorem batchC05120MinusMidpointP000DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP000Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP000RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP000Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP000Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP000Rounded2559]

def batchC05120MinusMidpointP001Rounded2559 : RatPair2542 :=
  ((((-183123827035311472519) : ℚ) /
        1267650600228229401496703205376),
    ((4644350003859797493 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120MinusMidpointP001Radius2559 : ℝ := ((2163081301365505 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC05120MinusMidpointP001RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP001Factor2559
        batchC05120MinusMidpointP001Center2559) =
        batchC05120MinusMidpointP001Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP001RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP001Rounded2559‖ ≤
          batchC05120MinusMidpointP001Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP001Factor2559
      batchC05120MinusMidpointP001Center2559)
  rw [batchC05120MinusMidpointP001RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP001Factor2559 * embedPair2542
        batchC05120MinusMidpointP001Center2559)
    (embedPair2542 batchC05120MinusMidpointP001Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP001DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP001Factor2559,
      batchC05120MinusMidpointP001Error2559, rounding2542,
      batchC05120MinusMidpointP001Radius2559]

theorem batchC05120MinusMidpointP001DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP001Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP001RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP001Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP001Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP001Rounded2559]

def batchC05120MinusMidpointP002Rounded2559 : RatPair2542 :=
  ((((-91441912838587249785) : ℚ) /
        633825300114114700748351602688),
    (((-9270578571827578657) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120MinusMidpointP002Radius2559 : ℝ := ((8640706324381803 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120MinusMidpointP002RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP002Factor2559
        batchC05120MinusMidpointP002Center2559) =
        batchC05120MinusMidpointP002Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP002RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP002Rounded2559‖ ≤
          batchC05120MinusMidpointP002Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP002Factor2559
      batchC05120MinusMidpointP002Center2559)
  rw [batchC05120MinusMidpointP002RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP002Factor2559 * embedPair2542
        batchC05120MinusMidpointP002Center2559)
    (embedPair2542 batchC05120MinusMidpointP002Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP002DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP002Factor2559,
      batchC05120MinusMidpointP002Error2559, rounding2542,
      batchC05120MinusMidpointP002Radius2559]

theorem batchC05120MinusMidpointP002DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP002Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP002RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP002Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP002Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP002Rounded2559]

def batchC05120MinusMidpointP003Rounded2559 : RatPair2542 :=
  ((((-91374821108900397591) : ℚ) /
        633825300114114700748351602688),
    (((-9260446983368458249) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120MinusMidpointP003Radius2559 : ℝ := ((17268420542842551 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP003RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP003Factor2559
        batchC05120MinusMidpointP003Center2559) =
        batchC05120MinusMidpointP003Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP003RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP003Rounded2559‖ ≤
          batchC05120MinusMidpointP003Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP003Factor2559
      batchC05120MinusMidpointP003Center2559)
  rw [batchC05120MinusMidpointP003RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP003Factor2559 * embedPair2542
        batchC05120MinusMidpointP003Center2559)
    (embedPair2542 batchC05120MinusMidpointP003Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP003DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP003Factor2559,
      batchC05120MinusMidpointP003Error2559, rounding2542,
      batchC05120MinusMidpointP003Radius2559]

theorem batchC05120MinusMidpointP003DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP003Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP003RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP003Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP003Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP003Rounded2559]

def batchC05120MinusMidpointP004Rounded2559 : RatPair2542 :=
  ((((-45667476606339097491) : ℚ) /
        316912650057057350374175801344),
    ((4627213247855488897 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120MinusMidpointP004Radius2559 : ℝ := ((4315175062103317 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05120MinusMidpointP004RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP004Factor2559
        batchC05120MinusMidpointP004Center2559) =
        batchC05120MinusMidpointP004Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP004RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP004Rounded2559‖ ≤
          batchC05120MinusMidpointP004Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP004Factor2559
      batchC05120MinusMidpointP004Center2559)
  rw [batchC05120MinusMidpointP004RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP004Factor2559 * embedPair2542
        batchC05120MinusMidpointP004Center2559)
    (embedPair2542 batchC05120MinusMidpointP004Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP004DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP004Factor2559,
      batchC05120MinusMidpointP004Error2559, rounding2542,
      batchC05120MinusMidpointP004Radius2559]

theorem batchC05120MinusMidpointP004DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP004Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP004RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP004Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP004Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP004Rounded2559]

def batchC05120MinusMidpointP005Rounded2559 : RatPair2542 :=
  ((((-842735506285587) : ℚ) /
        1237940039285380274899124224),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusMidpointP005Radius2559 : ℝ := ((39866895854283 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120MinusMidpointP005RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP005Factor2559
        batchC05120MinusMidpointP005Center2559) =
        batchC05120MinusMidpointP005Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP005RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP005Rounded2559‖ ≤
          batchC05120MinusMidpointP005Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP005Factor2559
      batchC05120MinusMidpointP005Center2559)
  rw [batchC05120MinusMidpointP005RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP005Factor2559 * embedPair2542
        batchC05120MinusMidpointP005Center2559)
    (embedPair2542 batchC05120MinusMidpointP005Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP005DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP005Factor2559,
      batchC05120MinusMidpointP005Error2559, rounding2542,
      batchC05120MinusMidpointP005Radius2559]

theorem batchC05120MinusMidpointP005DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP005Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP005RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP005Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP005Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP005Rounded2559]

def batchC05120MinusMidpointP006Rounded2559 : RatPair2542 :=
  ((((-414758502794930833) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusMidpointP006Radius2559 : ℝ := ((9865993104913 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05120MinusMidpointP006RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP006Factor2559
        batchC05120MinusMidpointP006Center2559) =
        batchC05120MinusMidpointP006Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP006RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP006Rounded2559‖ ≤
          batchC05120MinusMidpointP006Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP006Factor2559
      batchC05120MinusMidpointP006Center2559)
  rw [batchC05120MinusMidpointP006RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP006Factor2559 * embedPair2542
        batchC05120MinusMidpointP006Center2559)
    (embedPair2542 batchC05120MinusMidpointP006Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP006DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP006Factor2559,
      batchC05120MinusMidpointP006Error2559, rounding2542,
      batchC05120MinusMidpointP006Radius2559]

theorem batchC05120MinusMidpointP006DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP006Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP006RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP006Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP006Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP006Rounded2559]

def batchC05120MinusMidpointP007Rounded2559 : RatPair2542 :=
  ((((-1685897546449555) : ℚ) /
        9903520314283042199192993792),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120MinusMidpointP007Radius2559 : ℝ := ((21587620027015 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP007RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP007Factor2559
        batchC05120MinusMidpointP007Center2559) =
        batchC05120MinusMidpointP007Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP007RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP007Rounded2559‖ ≤
          batchC05120MinusMidpointP007Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP007Factor2559
      batchC05120MinusMidpointP007Center2559)
  rw [batchC05120MinusMidpointP007RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP007Factor2559 * embedPair2542
        batchC05120MinusMidpointP007Center2559)
    (embedPair2542 batchC05120MinusMidpointP007Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP007DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP007Factor2559,
      batchC05120MinusMidpointP007Error2559, rounding2542,
      batchC05120MinusMidpointP007Radius2559]

theorem batchC05120MinusMidpointP007DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP007Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP007RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP007Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP007Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP007Rounded2559]

def batchC05120MinusMidpointP008Rounded2559 : RatPair2542 :=
  ((((-24387043979485470259) : ℚ) /
        1267650600228229401496703205376),
    ((1910252087702901271 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120MinusMidpointP008Radius2559 : ℝ := ((2367147148235623 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP008RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP008Factor2559
        batchC05120MinusMidpointP008Center2559) =
        batchC05120MinusMidpointP008Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP008RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP008Rounded2559‖ ≤
          batchC05120MinusMidpointP008Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP008Factor2559
      batchC05120MinusMidpointP008Center2559)
  rw [batchC05120MinusMidpointP008RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP008Factor2559 * embedPair2542
        batchC05120MinusMidpointP008Center2559)
    (embedPair2542 batchC05120MinusMidpointP008Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP008DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP008Factor2559,
      batchC05120MinusMidpointP008Error2559, rounding2542,
      batchC05120MinusMidpointP008Radius2559]

theorem batchC05120MinusMidpointP008DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP008Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP008RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP008Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP008Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP008Rounded2559]

def batchC05120MinusMidpointP009Rounded2559 : RatPair2542 :=
  ((((-53078097490258622751) : ℚ) /
        1267650600228229401496703205376),
    ((3227216575070387647 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120MinusMidpointP009Radius2559 : ℝ := ((5065632118562215 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP009RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP009Factor2559
        batchC05120MinusMidpointP009Center2559) =
        batchC05120MinusMidpointP009Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP009RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP009Rounded2559‖ ≤
          batchC05120MinusMidpointP009Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP009Factor2559
      batchC05120MinusMidpointP009Center2559)
  rw [batchC05120MinusMidpointP009RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP009Factor2559 * embedPair2542
        batchC05120MinusMidpointP009Center2559)
    (embedPair2542 batchC05120MinusMidpointP009Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP009DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP009Factor2559,
      batchC05120MinusMidpointP009Error2559, rounding2542,
      batchC05120MinusMidpointP009Radius2559]

theorem batchC05120MinusMidpointP009DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP009Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP009RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP009Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP009Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP009Rounded2559]

def batchC05120MinusMidpointP010Rounded2559 : RatPair2542 :=
  ((((-18708314753878431687) : ℚ) /
        316912650057057350374175801344),
    ((2093980331483805165 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120MinusMidpointP010Radius2559 : ℝ := ((7108287657160417 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP010RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP010Factor2559
        batchC05120MinusMidpointP010Center2559) =
        batchC05120MinusMidpointP010Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP010RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP010Rounded2559‖ ≤
          batchC05120MinusMidpointP010Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP010Factor2559
      batchC05120MinusMidpointP010Center2559)
  rw [batchC05120MinusMidpointP010RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP010Factor2559 * embedPair2542
        batchC05120MinusMidpointP010Center2559)
    (embedPair2542 batchC05120MinusMidpointP010Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP010DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP010Factor2559,
      batchC05120MinusMidpointP010Error2559, rounding2542,
      batchC05120MinusMidpointP010Radius2559]

theorem batchC05120MinusMidpointP010DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP010Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP010RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP010Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP010Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP010Rounded2559]

def batchC05120MinusMidpointP011Rounded2559 : RatPair2542 :=
  ((((-45715913862793179905) : ℚ) /
        633825300114114700748351602688),
    ((1231842928870479081 : ℚ) /
        316912650057057350374175801344))

noncomputable def batchC05120MinusMidpointP011Radius2559 : ℝ := ((4333665749232653 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120MinusMidpointP011RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP011Factor2559
        batchC05120MinusMidpointP011Center2559) =
        batchC05120MinusMidpointP011Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP011RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP011Rounded2559‖ ≤
          batchC05120MinusMidpointP011Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP011Factor2559
      batchC05120MinusMidpointP011Center2559)
  rw [batchC05120MinusMidpointP011RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP011Factor2559 * embedPair2542
        batchC05120MinusMidpointP011Center2559)
    (embedPair2542 batchC05120MinusMidpointP011Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP011DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP011Factor2559,
      batchC05120MinusMidpointP011Error2559, rounding2542,
      batchC05120MinusMidpointP011Radius2559]

theorem batchC05120MinusMidpointP011DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP011Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP011RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP011Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP011Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP011Rounded2559]

def batchC05120MinusMidpointP012Rounded2559 : RatPair2542 :=
  ((((-55194767719301085481) : ℚ) /
        633825300114114700748351602688),
    ((180851083098893683 : ℚ) /
        39614081257132168796771975168))

noncomputable def batchC05120MinusMidpointP012Radius2559 : ℝ := ((5224669312317479 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120MinusMidpointP012RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP012Factor2559
        batchC05120MinusMidpointP012Center2559) =
        batchC05120MinusMidpointP012Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP012RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP012Rounded2559‖ ≤
          batchC05120MinusMidpointP012Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP012Factor2559
      batchC05120MinusMidpointP012Center2559)
  rw [batchC05120MinusMidpointP012RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP012Factor2559 * embedPair2542
        batchC05120MinusMidpointP012Center2559)
    (embedPair2542 batchC05120MinusMidpointP012Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP012DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP012Factor2559,
      batchC05120MinusMidpointP012Error2559, rounding2542,
      batchC05120MinusMidpointP012Radius2559]

theorem batchC05120MinusMidpointP012DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP012Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP012RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP012Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP012Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP012Rounded2559]

def batchC05120MinusMidpointP013Rounded2559 : RatPair2542 :=
  ((((-129229774835529403679) : ℚ) /
        1267650600228229401496703205376),
    ((416379209172197561 : ℚ) /
        79228162514264337593543950336))

noncomputable def batchC05120MinusMidpointP013Radius2559 : ℝ := ((12222137704973917 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP013RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP013Factor2559
        batchC05120MinusMidpointP013Center2559) =
        batchC05120MinusMidpointP013Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP013RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP013Rounded2559‖ ≤
          batchC05120MinusMidpointP013Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP013Factor2559
      batchC05120MinusMidpointP013Center2559)
  rw [batchC05120MinusMidpointP013RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP013Factor2559 * embedPair2542
        batchC05120MinusMidpointP013Center2559)
    (embedPair2542 batchC05120MinusMidpointP013Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP013DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP013Factor2559,
      batchC05120MinusMidpointP013Error2559, rounding2542,
      batchC05120MinusMidpointP013Radius2559]

theorem batchC05120MinusMidpointP013DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP013Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP013RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP013Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP013Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP013Rounded2559]

def batchC05120MinusMidpointP014Rounded2559 : RatPair2542 :=
  ((((-168080548783185617777) : ℚ) /
        1267650600228229401496703205376),
    ((8538072866309393719 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120MinusMidpointP014Radius2559 : ℝ := ((7942199100551321 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120MinusMidpointP014RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP014Factor2559
        batchC05120MinusMidpointP014Center2559) =
        batchC05120MinusMidpointP014Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP014RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP014Rounded2559‖ ≤
          batchC05120MinusMidpointP014Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP014Factor2559
      batchC05120MinusMidpointP014Center2559)
  rw [batchC05120MinusMidpointP014RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP014Factor2559 * embedPair2542
        batchC05120MinusMidpointP014Center2559)
    (embedPair2542 batchC05120MinusMidpointP014Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP014DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP014Factor2559,
      batchC05120MinusMidpointP014Error2559, rounding2542,
      batchC05120MinusMidpointP014Radius2559]

theorem batchC05120MinusMidpointP014DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP014Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP014RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP014Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP014Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP014Rounded2559]

def batchC05120MinusMidpointP015Rounded2559 : RatPair2542 :=
  ((((-199064889149410510645) : ℚ) /
        1267650600228229401496703205376),
    ((10107114908069524871 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120MinusMidpointP015Radius2559 : ℝ := ((18811784066313875 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP015RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP015Factor2559
        batchC05120MinusMidpointP015Center2559) =
        batchC05120MinusMidpointP015Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP015RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP015Rounded2559‖ ≤
          batchC05120MinusMidpointP015Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP015Factor2559
      batchC05120MinusMidpointP015Center2559)
  rw [batchC05120MinusMidpointP015RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP015Factor2559 * embedPair2542
        batchC05120MinusMidpointP015Center2559)
    (embedPair2542 batchC05120MinusMidpointP015Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP015DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP015Factor2559,
      batchC05120MinusMidpointP015Error2559, rounding2542,
      batchC05120MinusMidpointP015Radius2559]

theorem batchC05120MinusMidpointP015DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP015Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP015RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP015Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP015Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP015Rounded2559]

def batchC05120MinusMidpointP016Rounded2559 : RatPair2542 :=
  ((((-55772940637700088551) : ℚ) /
        316912650057057350374175801344),
    ((5684388929197747991 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120MinusMidpointP016Radius2559 : ℝ := ((2635743859691231 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC05120MinusMidpointP016RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP016Factor2559
        batchC05120MinusMidpointP016Center2559) =
        batchC05120MinusMidpointP016Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP016RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP016Rounded2559‖ ≤
          batchC05120MinusMidpointP016Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP016Factor2559
      batchC05120MinusMidpointP016Center2559)
  rw [batchC05120MinusMidpointP016RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP016Factor2559 * embedPair2542
        batchC05120MinusMidpointP016Center2559)
    (embedPair2542 batchC05120MinusMidpointP016Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP016DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP016Factor2559,
      batchC05120MinusMidpointP016Error2559, rounding2542,
      batchC05120MinusMidpointP016Radius2559]

theorem batchC05120MinusMidpointP016DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP016Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP016RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP016Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP016Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP016Rounded2559]

def batchC05120MinusMidpointP017Rounded2559 : RatPair2542 :=
  ((((-68420421411826435151) : ℚ) /
        316912650057057350374175801344),
    ((3537989969640805947 : ℚ) /
        316912650057057350374175801344))

noncomputable def batchC05120MinusMidpointP017Radius2559 : ℝ := ((12942995242491967 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120MinusMidpointP017RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP017Factor2559
        batchC05120MinusMidpointP017Center2559) =
        batchC05120MinusMidpointP017Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP017RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP017Rounded2559‖ ≤
          batchC05120MinusMidpointP017Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP017Factor2559
      batchC05120MinusMidpointP017Center2559)
  rw [batchC05120MinusMidpointP017RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP017Factor2559 * embedPair2542
        batchC05120MinusMidpointP017Center2559)
    (embedPair2542 batchC05120MinusMidpointP017Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP017DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP017Factor2559,
      batchC05120MinusMidpointP017Error2559, rounding2542,
      batchC05120MinusMidpointP017Radius2559]

theorem batchC05120MinusMidpointP017DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP017Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP017RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP017Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP017Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP017Rounded2559]

def batchC05120MinusMidpointP018Rounded2559 : RatPair2542 :=
  ((((-294156232294050812541) : ℚ) /
        1267650600228229401496703205376),
    ((15326228224883268117 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120MinusMidpointP018Radius2559 : ℝ := ((6958265178160289 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05120MinusMidpointP018RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP018Factor2559
        batchC05120MinusMidpointP018Center2559) =
        batchC05120MinusMidpointP018Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP018RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP018Rounded2559‖ ≤
          batchC05120MinusMidpointP018Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP018Factor2559
      batchC05120MinusMidpointP018Center2559)
  rw [batchC05120MinusMidpointP018RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP018Factor2559 * embedPair2542
        batchC05120MinusMidpointP018Center2559)
    (embedPair2542 batchC05120MinusMidpointP018Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP018DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP018Factor2559,
      batchC05120MinusMidpointP018Error2559, rounding2542,
      batchC05120MinusMidpointP018Radius2559]

theorem batchC05120MinusMidpointP018DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP018Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP018RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP018Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP018Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP018Rounded2559]

def batchC05120MinusMidpointP019Rounded2559 : RatPair2542 :=
  ((((-83258578049050380147) : ℚ) /
        316912650057057350374175801344),
    ((550933366705933677 : ℚ) /
        39614081257132168796771975168))

noncomputable def batchC05120MinusMidpointP019Radius2559 : ℝ := ((31537094891650129 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP019RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP019Factor2559
        batchC05120MinusMidpointP019Center2559) =
        batchC05120MinusMidpointP019Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP019RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP019Rounded2559‖ ≤
          batchC05120MinusMidpointP019Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP019Factor2559
      batchC05120MinusMidpointP019Center2559)
  rw [batchC05120MinusMidpointP019RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP019Factor2559 * embedPair2542
        batchC05120MinusMidpointP019Center2559)
    (embedPair2542 batchC05120MinusMidpointP019Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP019DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP019Factor2559,
      batchC05120MinusMidpointP019Error2559, rounding2542,
      batchC05120MinusMidpointP019Radius2559]

theorem batchC05120MinusMidpointP019DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP019Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP019RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP019Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP019Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP019Rounded2559]

def batchC05120MinusMidpointP020Rounded2559 : RatPair2542 :=
  ((((-189025057303334293291) : ℚ) /
        633825300114114700748351602688),
    ((637963321554917809 : ℚ) /
        39614081257132168796771975168))

noncomputable def batchC05120MinusMidpointP020Radius2559 : ℝ := ((35836813814868405 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP020RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP020Factor2559
        batchC05120MinusMidpointP020Center2559) =
        batchC05120MinusMidpointP020Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP020RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP020Rounded2559‖ ≤
          batchC05120MinusMidpointP020Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP020Factor2559
      batchC05120MinusMidpointP020Center2559)
  rw [batchC05120MinusMidpointP020RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP020Factor2559 * embedPair2542
        batchC05120MinusMidpointP020Center2559)
    (embedPair2542 batchC05120MinusMidpointP020Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP020DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP020Factor2559,
      batchC05120MinusMidpointP020Error2559, rounding2542,
      batchC05120MinusMidpointP020Radius2559]

theorem batchC05120MinusMidpointP020DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP020Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP020RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP020Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP020Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP020Rounded2559]

def batchC05120MinusMidpointP021Rounded2559 : RatPair2542 :=
  ((((-417801127040212980087) : ℚ) /
        1267650600228229401496703205376),
    ((11487827151294362725 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120MinusMidpointP021Radius2559 : ℝ := ((39643126884540141 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP021RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP021Factor2559
        batchC05120MinusMidpointP021Center2559) =
        batchC05120MinusMidpointP021Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP021RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP021Rounded2559‖ ≤
          batchC05120MinusMidpointP021Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP021Factor2559
      batchC05120MinusMidpointP021Center2559)
  rw [batchC05120MinusMidpointP021RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP021Factor2559 * embedPair2542
        batchC05120MinusMidpointP021Center2559)
    (embedPair2542 batchC05120MinusMidpointP021Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP021DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP021Factor2559,
      batchC05120MinusMidpointP021Error2559, rounding2542,
      batchC05120MinusMidpointP021Radius2559]

theorem batchC05120MinusMidpointP021DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP021Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP021RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP021Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP021Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP021Rounded2559]

def batchC05120MinusMidpointP022Rounded2559 : RatPair2542 :=
  ((((-438915514999415869391) : ℚ) /
        1267650600228229401496703205376),
    ((12186783147121564567 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120MinusMidpointP022Radius2559 : ℝ := ((41668431869067903 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP022RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP022Factor2559
        batchC05120MinusMidpointP022Center2559) =
        batchC05120MinusMidpointP022Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP022RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP022Rounded2559‖ ≤
          batchC05120MinusMidpointP022Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP022Factor2559
      batchC05120MinusMidpointP022Center2559)
  rw [batchC05120MinusMidpointP022RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP022Factor2559 * embedPair2542
        batchC05120MinusMidpointP022Center2559)
    (embedPair2542 batchC05120MinusMidpointP022Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP022DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP022Factor2559,
      batchC05120MinusMidpointP022Error2559, rounding2542,
      batchC05120MinusMidpointP022Radius2559]

theorem batchC05120MinusMidpointP022DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP022Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP022RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP022Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP022Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP022Rounded2559]

def batchC05120MinusMidpointP023Rounded2559 : RatPair2542 :=
  ((((-62837918632044822619) : ℚ) /
        158456325028528675187087900672),
    ((28750664364502420925 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120MinusMidpointP023Radius2559 : ℝ := ((47801421728456613 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP023RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP023Factor2559
        batchC05120MinusMidpointP023Center2559) =
        batchC05120MinusMidpointP023Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP023RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP023Rounded2559‖ ≤
          batchC05120MinusMidpointP023Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP023Factor2559
      batchC05120MinusMidpointP023Center2559)
  rw [batchC05120MinusMidpointP023RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP023Factor2559 * embedPair2542
        batchC05120MinusMidpointP023Center2559)
    (embedPair2542 batchC05120MinusMidpointP023Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP023DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP023Factor2559,
      batchC05120MinusMidpointP023Error2559, rounding2542,
      batchC05120MinusMidpointP023Radius2559]

theorem batchC05120MinusMidpointP023DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP023Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP023RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP023Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP023Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP023Rounded2559]

def batchC05120MinusMidpointP024Rounded2559 : RatPair2542 :=
  ((((-533466877520828668447) : ℚ) /
        1267650600228229401496703205376),
    ((15471018044793325021 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120MinusMidpointP024Radius2559 : ℝ := ((793231022766363 : ℝ) /
        (2 * 10^40
        + 1778071482940061661655974875633165533184))

theorem batchC05120MinusMidpointP024RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP024Factor2559
        batchC05120MinusMidpointP024Center2559) =
        batchC05120MinusMidpointP024Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP024RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP024Rounded2559‖ ≤
          batchC05120MinusMidpointP024Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP024Factor2559
      batchC05120MinusMidpointP024Center2559)
  rw [batchC05120MinusMidpointP024RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP024Factor2559 * embedPair2542
        batchC05120MinusMidpointP024Center2559)
    (embedPair2542 batchC05120MinusMidpointP024Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP024DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP024Factor2559,
      batchC05120MinusMidpointP024Error2559, rounding2542,
      batchC05120MinusMidpointP024Radius2559]

theorem batchC05120MinusMidpointP024DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP024Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP024RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP024Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP024Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP024Rounded2559]

def batchC05120MinusMidpointP025Rounded2559 : RatPair2542 :=
  ((((-17916485924935400725) : ℚ) /
        39614081257132168796771975168),
    ((33856833337743764657 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120MinusMidpointP025Radius2559 : ℝ := ((54616147744855189 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP025RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP025Factor2559
        batchC05120MinusMidpointP025Center2559) =
        batchC05120MinusMidpointP025Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP025RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP025Rounded2559‖ ≤
          batchC05120MinusMidpointP025Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP025Factor2559
      batchC05120MinusMidpointP025Center2559)
  rw [batchC05120MinusMidpointP025RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP025Factor2559 * embedPair2542
        batchC05120MinusMidpointP025Center2559)
    (embedPair2542 batchC05120MinusMidpointP025Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP025DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP025Factor2559,
      batchC05120MinusMidpointP025Error2559, rounding2542,
      batchC05120MinusMidpointP025Radius2559]

theorem batchC05120MinusMidpointP025DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP025Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP025RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP025Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP025Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP025Rounded2559]

def batchC05120MinusMidpointP026Rounded2559 : RatPair2542 :=
  ((((-615544534469100603829) : ℚ) /
        1267650600228229401496703205376),
    ((18517236963327370277 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120MinusMidpointP026Radius2559 : ℝ := ((29350805287237851 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120MinusMidpointP026RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP026Factor2559
        batchC05120MinusMidpointP026Center2559) =
        batchC05120MinusMidpointP026Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP026RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP026Rounded2559‖ ≤
          batchC05120MinusMidpointP026Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP026Factor2559
      batchC05120MinusMidpointP026Center2559)
  rw [batchC05120MinusMidpointP026RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP026Factor2559 * embedPair2542
        batchC05120MinusMidpointP026Center2559)
    (embedPair2542 batchC05120MinusMidpointP026Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP026DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP026Factor2559,
      batchC05120MinusMidpointP026Error2559, rounding2542,
      batchC05120MinusMidpointP026Radius2559]

theorem batchC05120MinusMidpointP026DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP026Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP026RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP026Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP026Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP026Rounded2559]

def batchC05120MinusMidpointP027Rounded2559 : RatPair2542 :=
  ((((-84887821864139210491) : ℚ) /
        158456325028528675187087900672),
    ((20994406646714085209 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120MinusMidpointP027Radius2559 : ℝ := ((64868447477782239 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP027RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP027Factor2559
        batchC05120MinusMidpointP027Center2559) =
        batchC05120MinusMidpointP027Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP027RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP027Rounded2559‖ ≤
          batchC05120MinusMidpointP027Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP027Factor2559
      batchC05120MinusMidpointP027Center2559)
  rw [batchC05120MinusMidpointP027RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP027Factor2559 * embedPair2542
        batchC05120MinusMidpointP027Center2559)
    (embedPair2542 batchC05120MinusMidpointP027Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP027DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP027Factor2559,
      batchC05120MinusMidpointP027Error2559, rounding2542,
      batchC05120MinusMidpointP027Radius2559]

theorem batchC05120MinusMidpointP027DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP027Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP027RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP027Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP027Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP027Rounded2559]

def batchC05120MinusMidpointP028Rounded2559 : RatPair2542 :=
  ((((-44070418092728592457) : ℚ) /
        79228162514264337593543950336),
    ((22037464521523085369 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120MinusMidpointP028Radius2559 : ℝ := ((67398949321974451 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP028RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP028Factor2559
        batchC05120MinusMidpointP028Center2559) =
        batchC05120MinusMidpointP028Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP028RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP028Rounded2559‖ ≤
          batchC05120MinusMidpointP028Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP028Factor2559
      batchC05120MinusMidpointP028Center2559)
  rw [batchC05120MinusMidpointP028RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP028Factor2559 * embedPair2542
        batchC05120MinusMidpointP028Center2559)
    (embedPair2542 batchC05120MinusMidpointP028Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP028DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP028Factor2559,
      batchC05120MinusMidpointP028Error2559, rounding2542,
      batchC05120MinusMidpointP028Radius2559]

theorem batchC05120MinusMidpointP028DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP028Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP028RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP028Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP028Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP028Rounded2559]

def batchC05120MinusMidpointP029Rounded2559 : RatPair2542 :=
  ((((-745683670130948457301) : ℚ) /
        1267650600228229401496703205376),
    ((47391021353301108757 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120MinusMidpointP029Radius2559 : ℝ := ((71348768808934797 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120MinusMidpointP029RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120MinusMidpointP029Factor2559
        batchC05120MinusMidpointP029Center2559) =
        batchC05120MinusMidpointP029Rounded2559 := by
  cbv

theorem batchC05120MinusMidpointP029RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05120MinusMidpointPosition2559 -
      embedPair2542 batchC05120MinusMidpointP029Rounded2559‖ ≤
          batchC05120MinusMidpointP029Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120MinusMidpointP029Factor2559
      batchC05120MinusMidpointP029Center2559)
  rw [batchC05120MinusMidpointP029RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP029Factor2559 * embedPair2542
        batchC05120MinusMidpointP029Center2559)
    (embedPair2542 batchC05120MinusMidpointP029Rounded2559)).trans (add_le_add
        batchC05120MinusMidpointP029DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120MinusMidpointP029Factor2559,
      batchC05120MinusMidpointP029Error2559, rounding2542,
      batchC05120MinusMidpointP029Radius2559]

theorem batchC05120MinusMidpointP029DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05120MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05120MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05120MinusMidpointPosition2559)
    (embedPair2542 batchC05120MinusMidpointP029Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120MinusMidpointP029RoundedError2559
      (embedPair_magnitude2542
      batchC05120MinusMidpointP029Rounded2559))
  apply h'.trans
  norm_num [batchC05120MinusMidpointP029Radius2559, pairMagnitude2542,
      batchC05120MinusMidpointP029Rounded2559]

noncomputable def batchC05120MinusSignedMidpointValue2559 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchC05120MinusMidpointP000Rounded2559
  | 1 => embedPair2542 batchC05120MinusMidpointP001Rounded2559
  | 2 => embedPair2542 batchC05120MinusMidpointP002Rounded2559
  | 3 => embedPair2542 batchC05120MinusMidpointP003Rounded2559
  | 4 => embedPair2542 batchC05120MinusMidpointP004Rounded2559
  | 5 => embedPair2542 batchC05120MinusMidpointP005Rounded2559
  | 6 => embedPair2542 batchC05120MinusMidpointP006Rounded2559
  | 7 => embedPair2542 batchC05120MinusMidpointP007Rounded2559
  | 8 => embedPair2542 batchC05120MinusMidpointP008Rounded2559
  | 9 => embedPair2542 batchC05120MinusMidpointP009Rounded2559
  | 10 => embedPair2542 batchC05120MinusMidpointP010Rounded2559
  | 11 => embedPair2542 batchC05120MinusMidpointP011Rounded2559
  | 12 => embedPair2542 batchC05120MinusMidpointP012Rounded2559
  | 13 => embedPair2542 batchC05120MinusMidpointP013Rounded2559
  | 14 => embedPair2542 batchC05120MinusMidpointP014Rounded2559
  | 15 => embedPair2542 batchC05120MinusMidpointP015Rounded2559
  | 16 => embedPair2542 batchC05120MinusMidpointP016Rounded2559
  | 17 => embedPair2542 batchC05120MinusMidpointP017Rounded2559
  | 18 => embedPair2542 batchC05120MinusMidpointP018Rounded2559
  | 19 => embedPair2542 batchC05120MinusMidpointP019Rounded2559
  | 20 => embedPair2542 batchC05120MinusMidpointP020Rounded2559
  | 21 => embedPair2542 batchC05120MinusMidpointP021Rounded2559
  | 22 => embedPair2542 batchC05120MinusMidpointP022Rounded2559
  | 23 => embedPair2542 batchC05120MinusMidpointP023Rounded2559
  | 24 => embedPair2542 batchC05120MinusMidpointP024Rounded2559
  | 25 => embedPair2542 batchC05120MinusMidpointP025Rounded2559
  | 26 => embedPair2542 batchC05120MinusMidpointP026Rounded2559
  | 27 => embedPair2542 batchC05120MinusMidpointP027Rounded2559
  | 28 => embedPair2542 batchC05120MinusMidpointP028Rounded2559
  | 29 => embedPair2542 batchC05120MinusMidpointP029Rounded2559
  | _ => 0

noncomputable def batchC05120MinusSignedMidpointError2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05120MinusMidpointP000Radius2559
  | 1 => batchC05120MinusMidpointP001Radius2559
  | 2 => batchC05120MinusMidpointP002Radius2559
  | 3 => batchC05120MinusMidpointP003Radius2559
  | 4 => batchC05120MinusMidpointP004Radius2559
  | 5 => batchC05120MinusMidpointP005Radius2559
  | 6 => batchC05120MinusMidpointP006Radius2559
  | 7 => batchC05120MinusMidpointP007Radius2559
  | 8 => batchC05120MinusMidpointP008Radius2559
  | 9 => batchC05120MinusMidpointP009Radius2559
  | 10 => batchC05120MinusMidpointP010Radius2559
  | 11 => batchC05120MinusMidpointP011Radius2559
  | 12 => batchC05120MinusMidpointP012Radius2559
  | 13 => batchC05120MinusMidpointP013Radius2559
  | 14 => batchC05120MinusMidpointP014Radius2559
  | 15 => batchC05120MinusMidpointP015Radius2559
  | 16 => batchC05120MinusMidpointP016Radius2559
  | 17 => batchC05120MinusMidpointP017Radius2559
  | 18 => batchC05120MinusMidpointP018Radius2559
  | 19 => batchC05120MinusMidpointP019Radius2559
  | 20 => batchC05120MinusMidpointP020Radius2559
  | 21 => batchC05120MinusMidpointP021Radius2559
  | 22 => batchC05120MinusMidpointP022Radius2559
  | 23 => batchC05120MinusMidpointP023Radius2559
  | 24 => batchC05120MinusMidpointP024Radius2559
  | 25 => batchC05120MinusMidpointP025Radius2559
  | 26 => batchC05120MinusMidpointP026Radius2559
  | 27 => batchC05120MinusMidpointP027Radius2559
  | 28 => batchC05120MinusMidpointP028Radius2559
  | 29 => batchC05120MinusMidpointP029Radius2559
  | _ => 0

theorem batchC05120MinusSignedMidpointExpError2559 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC05120MinusMidpointPosition2559 -
        batchC05120MinusSignedMidpointValue2559 i‖ ≤ batchC05120MinusSignedMidpointError2559 i :=
            by
  fin_cases i
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP000RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP001RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP002RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP003RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP004RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP005RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP006RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP007RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP008RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP009RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP010RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP011RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP012RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP013RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP014RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP015RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP016RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP017RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP018RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP019RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP020RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP021RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP022RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP023RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP024RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP025RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP026RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP027RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP028RoundedError2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP029RoundedError2559

theorem batchC05120MinusSignedMidpointUnitNorm2559 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC05120MinusMidpointPosition2559‖ ≤ 1
        := by
  fin_cases i
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP000DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP001DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP002DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP003DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP004DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP005DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP006DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP007DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP008DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP009DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP010DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP011DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP012DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP013DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP014DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP015DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP016DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP017DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP018DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP019DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP020DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP021DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP022DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP023DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP024DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP025DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP026DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP027DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP028DerivativeNorm2559
  · simpa only [batchC05120MinusSignedMidpointValue2559, batchC05120MinusSignedMidpointError2559]
      using
      batchC05120MinusMidpointP029DerivativeNorm2559

noncomputable def batchC05120MinusSignedMidpointSum2559 : ℂ := ⟨(((-(((1355081800147 * 10^40
        + 2097853585020424302614525643454381375646) * 10^40
        + 3263108756170397069319357569905255758123) * 10^40
        + 4890605035290216277162784176500365125401)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216)),
    (((((40867364175 * 10^40
        + 7681079026576078632466729421836300316377) * 10^40
        + 1216848333140008048415001224021186215085) * 10^40
        + 5465481928863002304499712518298161173449) : ℝ) /
        (((21661481 * 10^40
        + 9853188660904563608136178414330971646513) * 10^40
        + 7356699351937172355172896723145017999980) * 10^40
        + 47688590453885868835635965404913860608))⟩

noncomputable def batchC05120MinusSignedMidpointUpper2559 : ℝ := ((3133544989551 : ℝ) /
        100000000)

theorem batchC05120MinusSignedMidpointSum_eq2559 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchC05120MinusSignedMidpointValue2559 i) =
      batchC05120MinusSignedMidpointSum2559 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
        batchC05120MinusSignedMidpointValue2559,
      batchC05120MinusSignedMidpointSum2559, embedPair2542,
          batchC05120MinusMidpointP000Rounded2559,
      batchC05120MinusMidpointP001Rounded2559,
      batchC05120MinusMidpointP002Rounded2559,
      batchC05120MinusMidpointP003Rounded2559,
      batchC05120MinusMidpointP004Rounded2559,
      batchC05120MinusMidpointP005Rounded2559,
      batchC05120MinusMidpointP006Rounded2559,
      batchC05120MinusMidpointP007Rounded2559,
      batchC05120MinusMidpointP008Rounded2559,
      batchC05120MinusMidpointP009Rounded2559,
      batchC05120MinusMidpointP010Rounded2559,
      batchC05120MinusMidpointP011Rounded2559,
      batchC05120MinusMidpointP012Rounded2559,
      batchC05120MinusMidpointP013Rounded2559,
      batchC05120MinusMidpointP014Rounded2559,
      batchC05120MinusMidpointP015Rounded2559,
      batchC05120MinusMidpointP016Rounded2559,
      batchC05120MinusMidpointP017Rounded2559,
      batchC05120MinusMidpointP018Rounded2559,
      batchC05120MinusMidpointP019Rounded2559,
      batchC05120MinusMidpointP020Rounded2559,
      batchC05120MinusMidpointP021Rounded2559,
      batchC05120MinusMidpointP022Rounded2559,
      batchC05120MinusMidpointP023Rounded2559,
      batchC05120MinusMidpointP024Rounded2559,
      batchC05120MinusMidpointP025Rounded2559,
      batchC05120MinusMidpointP026Rounded2559,
      batchC05120MinusMidpointP027Rounded2559,
      batchC05120MinusMidpointP028Rounded2559,
      batchC05120MinusMidpointP029Rounded2559, Complex.mul_re, Complex.mul_im]

theorem batchC05120MinusSignedMidpointSum_norm2559 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC05120MinusSignedMidpointValue2559 i‖ ≤
        ((3133544989541 : ℝ)
        /
        100000000) := by
  rw [batchC05120MinusSignedMidpointSum_eq2559]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchC05120MinusSignedMidpointSum2559]

theorem batchC05120MinusSignedMidpointCharge2559 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchC05120MinusSignedMidpointError2559 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
      batchC05120MinusSignedMidpointError2559,
      batchC05120MinusMidpointP000Radius2559,
      batchC05120MinusMidpointP001Radius2559,
      batchC05120MinusMidpointP002Radius2559,
      batchC05120MinusMidpointP003Radius2559,
      batchC05120MinusMidpointP004Radius2559,
      batchC05120MinusMidpointP005Radius2559,
      batchC05120MinusMidpointP006Radius2559,
      batchC05120MinusMidpointP007Radius2559,
      batchC05120MinusMidpointP008Radius2559,
      batchC05120MinusMidpointP009Radius2559,
      batchC05120MinusMidpointP010Radius2559,
      batchC05120MinusMidpointP011Radius2559,
      batchC05120MinusMidpointP012Radius2559,
      batchC05120MinusMidpointP013Radius2559,
      batchC05120MinusMidpointP014Radius2559,
      batchC05120MinusMidpointP015Radius2559,
      batchC05120MinusMidpointP016Radius2559,
      batchC05120MinusMidpointP017Radius2559,
      batchC05120MinusMidpointP018Radius2559,
      batchC05120MinusMidpointP019Radius2559,
      batchC05120MinusMidpointP020Radius2559,
      batchC05120MinusMidpointP021Radius2559,
      batchC05120MinusMidpointP022Radius2559,
      batchC05120MinusMidpointP023Radius2559,
      batchC05120MinusMidpointP024Radius2559,
      batchC05120MinusMidpointP025Radius2559,
      batchC05120MinusMidpointP026Radius2559,
      batchC05120MinusMidpointP027Radius2559,
      batchC05120MinusMidpointP028Radius2559,
      batchC05120MinusMidpointP029Radius2559]

theorem batchC05120MinusSignedMidpointUpper_le2559 :
    signedJetUpper2539 2 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchC05120MinusMidpointPosition2559 ≤
          batchC05120MinusSignedMidpointUpper2559 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC05120MinusMidpointPosition2559‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC05120MinusSignedMidpointValue2559 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchC05120MinusSignedMidpointError2559 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (batchC05120MinusSignedMidpointExpError2559 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC05120MinusMidpointPosition2559‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchC05120MinusSignedMidpointUnitNorm2559 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC05120MinusMidpointPosition2559‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchC05120MinusSignedMidpointUpper2559
  linarith [batchC05120MinusSignedMidpointSum_norm2559, batchC05120MinusSignedMidpointCharge2559]

theorem batchC05120MinusPhysicalSecond2559 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        batchC05120MinusMidpointPosition2559‖ ≤
      batchC05120MinusSignedMidpointUpper2559 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchC05120MinusMidpointPosition2559
  exact h.trans batchC05120MinusSignedMidpointUpper_le2559

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05120MinusSignedMidpointExpError2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusSignedMidpointSum_eq2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusSignedMidpointCharge2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusSignedMidpointUpper_le2559
#print axioms ConnesWeilRH.Dev.batchC05120MinusPhysicalSecond2559
