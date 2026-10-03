import ConnesWeilRH.Dev.C1RouteABatchC05119PlusMidpoint2559

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem batchC05119PlusMidpoint_triangle2559 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def batchC05119PlusMidpointP000Rounded2559 : RatPair2542 :=
  ((((-5737111873938200909) : ℚ) /
        39614081257132168796771975168),
    (((-9323715983677776695) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP000Radius2559 : ℝ := ((8674776290749969 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119PlusMidpointP000RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP000Factor2559
        batchC05119PlusMidpointP000Center2559) =
        batchC05119PlusMidpointP000Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP000RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP000Rounded2559‖ ≤
          batchC05119PlusMidpointP000Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP000Factor2559
      batchC05119PlusMidpointP000Center2559)
  rw [batchC05119PlusMidpointP000RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP000Factor2559 * embedPair2542
        batchC05119PlusMidpointP000Center2559)
    (embedPair2542 batchC05119PlusMidpointP000Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP000DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP000Factor2559,
      batchC05119PlusMidpointP000Error2559, rounding2542,
      batchC05119PlusMidpointP000Radius2559]

theorem batchC05119PlusMidpointP000DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP000Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP000RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP000Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP000Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP000Rounded2559]

def batchC05119PlusMidpointP001Rounded2559 : RatPair2542 :=
  ((((-183123827035311472519) : ℚ) /
        1267650600228229401496703205376),
    (((-9288700007719594987) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP001Radius2559 : ℝ := ((2163081301365505 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC05119PlusMidpointP001RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP001Factor2559
        batchC05119PlusMidpointP001Center2559) =
        batchC05119PlusMidpointP001Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP001RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP001Rounded2559‖ ≤
          batchC05119PlusMidpointP001Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP001Factor2559
      batchC05119PlusMidpointP001Center2559)
  rw [batchC05119PlusMidpointP001RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP001Factor2559 * embedPair2542
        batchC05119PlusMidpointP001Center2559)
    (embedPair2542 batchC05119PlusMidpointP001Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP001DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP001Factor2559,
      batchC05119PlusMidpointP001Error2559, rounding2542,
      batchC05119PlusMidpointP001Radius2559]

theorem batchC05119PlusMidpointP001DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP001Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP001RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP001Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP001Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP001Rounded2559]

def batchC05119PlusMidpointP002Rounded2559 : RatPair2542 :=
  ((((-91441912838587249785) : ℚ) /
        633825300114114700748351602688),
    ((289705580369611833 : ℚ) /
        39614081257132168796771975168))

noncomputable def batchC05119PlusMidpointP002Radius2559 : ℝ := ((8640706324381803 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119PlusMidpointP002RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP002Factor2559
        batchC05119PlusMidpointP002Center2559) =
        batchC05119PlusMidpointP002Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP002RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP002Rounded2559‖ ≤
          batchC05119PlusMidpointP002Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP002Factor2559
      batchC05119PlusMidpointP002Center2559)
  rw [batchC05119PlusMidpointP002RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP002Factor2559 * embedPair2542
        batchC05119PlusMidpointP002Center2559)
    (embedPair2542 batchC05119PlusMidpointP002Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP002DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP002Factor2559,
      batchC05119PlusMidpointP002Error2559, rounding2542,
      batchC05119PlusMidpointP002Radius2559]

theorem batchC05119PlusMidpointP002DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP002Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP002RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP002Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP002Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP002Rounded2559]

def batchC05119PlusMidpointP003Rounded2559 : RatPair2542 :=
  ((((-91374821108900397591) : ℚ) /
        633825300114114700748351602688),
    ((1157555872921057281 : ℚ) /
        158456325028528675187087900672))

noncomputable def batchC05119PlusMidpointP003Radius2559 : ℝ := ((17268420542842551 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP003RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP003Factor2559
        batchC05119PlusMidpointP003Center2559) =
        batchC05119PlusMidpointP003Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP003RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP003Rounded2559‖ ≤
          batchC05119PlusMidpointP003Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP003Factor2559
      batchC05119PlusMidpointP003Center2559)
  rw [batchC05119PlusMidpointP003RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP003Factor2559 * embedPair2542
        batchC05119PlusMidpointP003Center2559)
    (embedPair2542 batchC05119PlusMidpointP003Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP003DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP003Factor2559,
      batchC05119PlusMidpointP003Error2559, rounding2542,
      batchC05119PlusMidpointP003Radius2559]

theorem batchC05119PlusMidpointP003DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP003Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP003RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP003Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP003Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP003Rounded2559]

def batchC05119PlusMidpointP004Rounded2559 : RatPair2542 :=
  ((((-45667476606339097491) : ℚ) /
        316912650057057350374175801344),
    (((-9254426495710977795) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP004Radius2559 : ℝ := ((4315175062103317 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05119PlusMidpointP004RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP004Factor2559
        batchC05119PlusMidpointP004Center2559) =
        batchC05119PlusMidpointP004Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP004RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP004Rounded2559‖ ≤
          batchC05119PlusMidpointP004Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP004Factor2559
      batchC05119PlusMidpointP004Center2559)
  rw [batchC05119PlusMidpointP004RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP004Factor2559 * embedPair2542
        batchC05119PlusMidpointP004Center2559)
    (embedPair2542 batchC05119PlusMidpointP004Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP004DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP004Factor2559,
      batchC05119PlusMidpointP004Error2559, rounding2542,
      batchC05119PlusMidpointP004Radius2559]

theorem batchC05119PlusMidpointP004DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP004Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP004RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP004Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP004Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP004Rounded2559]

def batchC05119PlusMidpointP005Rounded2559 : RatPair2542 :=
  ((((-842735506285587) : ℚ) /
        1237940039285380274899124224),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusMidpointP005Radius2559 : ℝ := ((39866895854283 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119PlusMidpointP005RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP005Factor2559
        batchC05119PlusMidpointP005Center2559) =
        batchC05119PlusMidpointP005Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP005RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP005Rounded2559‖ ≤
          batchC05119PlusMidpointP005Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP005Factor2559
      batchC05119PlusMidpointP005Center2559)
  rw [batchC05119PlusMidpointP005RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP005Factor2559 * embedPair2542
        batchC05119PlusMidpointP005Center2559)
    (embedPair2542 batchC05119PlusMidpointP005Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP005DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP005Factor2559,
      batchC05119PlusMidpointP005Error2559, rounding2542,
      batchC05119PlusMidpointP005Radius2559]

theorem batchC05119PlusMidpointP005DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP005Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP005RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP005Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP005Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP005Rounded2559]

def batchC05119PlusMidpointP006Rounded2559 : RatPair2542 :=
  ((((-414758502794930833) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusMidpointP006Radius2559 : ℝ := ((9865993104913 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05119PlusMidpointP006RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP006Factor2559
        batchC05119PlusMidpointP006Center2559) =
        batchC05119PlusMidpointP006Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP006RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP006Rounded2559‖ ≤
          batchC05119PlusMidpointP006Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP006Factor2559
      batchC05119PlusMidpointP006Center2559)
  rw [batchC05119PlusMidpointP006RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP006Factor2559 * embedPair2542
        batchC05119PlusMidpointP006Center2559)
    (embedPair2542 batchC05119PlusMidpointP006Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP006DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP006Factor2559,
      batchC05119PlusMidpointP006Error2559, rounding2542,
      batchC05119PlusMidpointP006Radius2559]

theorem batchC05119PlusMidpointP006DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP006Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP006RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP006Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP006Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP006Rounded2559]

def batchC05119PlusMidpointP007Rounded2559 : RatPair2542 :=
  ((((-1685897546449555) : ℚ) /
        9903520314283042199192993792),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119PlusMidpointP007Radius2559 : ℝ := ((21587620027015 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP007RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP007Factor2559
        batchC05119PlusMidpointP007Center2559) =
        batchC05119PlusMidpointP007Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP007RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP007Rounded2559‖ ≤
          batchC05119PlusMidpointP007Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP007Factor2559
      batchC05119PlusMidpointP007Center2559)
  rw [batchC05119PlusMidpointP007RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP007Factor2559 * embedPair2542
        batchC05119PlusMidpointP007Center2559)
    (embedPair2542 batchC05119PlusMidpointP007Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP007DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP007Factor2559,
      batchC05119PlusMidpointP007Error2559, rounding2542,
      batchC05119PlusMidpointP007Radius2559]

theorem batchC05119PlusMidpointP007DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP007Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP007RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP007Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP007Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP007Rounded2559]

def batchC05119PlusMidpointP008Rounded2559 : RatPair2542 :=
  ((((-24387043979485470259) : ℚ) /
        1267650600228229401496703205376),
    (((-238781510962862659) : ℚ) /
        158456325028528675187087900672))

noncomputable def batchC05119PlusMidpointP008Radius2559 : ℝ := ((2367147148235623 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP008RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP008Factor2559
        batchC05119PlusMidpointP008Center2559) =
        batchC05119PlusMidpointP008Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP008RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP008Rounded2559‖ ≤
          batchC05119PlusMidpointP008Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP008Factor2559
      batchC05119PlusMidpointP008Center2559)
  rw [batchC05119PlusMidpointP008RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP008Factor2559 * embedPair2542
        batchC05119PlusMidpointP008Center2559)
    (embedPair2542 batchC05119PlusMidpointP008Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP008DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP008Factor2559,
      batchC05119PlusMidpointP008Error2559, rounding2542,
      batchC05119PlusMidpointP008Radius2559]

theorem batchC05119PlusMidpointP008DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP008Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP008RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP008Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP008Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP008Rounded2559]

def batchC05119PlusMidpointP009Rounded2559 : RatPair2542 :=
  ((((-53078097490258622751) : ℚ) /
        1267650600228229401496703205376),
    (((-50425258985474807) : ℚ) /
        19807040628566084398385987584))

noncomputable def batchC05119PlusMidpointP009Radius2559 : ℝ := ((5065632118562215 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP009RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP009Factor2559
        batchC05119PlusMidpointP009Center2559) =
        batchC05119PlusMidpointP009Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP009RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP009Rounded2559‖ ≤
          batchC05119PlusMidpointP009Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP009Factor2559
      batchC05119PlusMidpointP009Center2559)
  rw [batchC05119PlusMidpointP009RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP009Factor2559 * embedPair2542
        batchC05119PlusMidpointP009Center2559)
    (embedPair2542 batchC05119PlusMidpointP009Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP009DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP009Factor2559,
      batchC05119PlusMidpointP009Error2559, rounding2542,
      batchC05119PlusMidpointP009Radius2559]

theorem batchC05119PlusMidpointP009DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP009Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP009RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP009Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP009Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP009Rounded2559]

def batchC05119PlusMidpointP010Rounded2559 : RatPair2542 :=
  ((((-18708314753878431687) : ℚ) /
        316912650057057350374175801344),
    (((-4187960662967610331) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP010Radius2559 : ℝ := ((7108287657160417 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP010RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP010Factor2559
        batchC05119PlusMidpointP010Center2559) =
        batchC05119PlusMidpointP010Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP010RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP010Rounded2559‖ ≤
          batchC05119PlusMidpointP010Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP010Factor2559
      batchC05119PlusMidpointP010Center2559)
  rw [batchC05119PlusMidpointP010RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP010Factor2559 * embedPair2542
        batchC05119PlusMidpointP010Center2559)
    (embedPair2542 batchC05119PlusMidpointP010Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP010DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP010Factor2559,
      batchC05119PlusMidpointP010Error2559, rounding2542,
      batchC05119PlusMidpointP010Radius2559]

theorem batchC05119PlusMidpointP010DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP010Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP010RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP010Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP010Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP010Rounded2559]

def batchC05119PlusMidpointP011Rounded2559 : RatPair2542 :=
  ((((-45715913862793179905) : ℚ) /
        633825300114114700748351602688),
    (((-4927371715481916325) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP011Radius2559 : ℝ := ((4333665749232653 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119PlusMidpointP011RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP011Factor2559
        batchC05119PlusMidpointP011Center2559) =
        batchC05119PlusMidpointP011Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP011RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP011Rounded2559‖ ≤
          batchC05119PlusMidpointP011Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP011Factor2559
      batchC05119PlusMidpointP011Center2559)
  rw [batchC05119PlusMidpointP011RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP011Factor2559 * embedPair2542
        batchC05119PlusMidpointP011Center2559)
    (embedPair2542 batchC05119PlusMidpointP011Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP011DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP011Factor2559,
      batchC05119PlusMidpointP011Error2559, rounding2542,
      batchC05119PlusMidpointP011Radius2559]

theorem batchC05119PlusMidpointP011DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP011Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP011RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP011Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP011Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP011Rounded2559]

def batchC05119PlusMidpointP012Rounded2559 : RatPair2542 :=
  ((((-55194767719301085481) : ℚ) /
        633825300114114700748351602688),
    (((-5787234659164597857) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP012Radius2559 : ℝ := ((5224669312317479 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119PlusMidpointP012RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP012Factor2559
        batchC05119PlusMidpointP012Center2559) =
        batchC05119PlusMidpointP012Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP012RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP012Rounded2559‖ ≤
          batchC05119PlusMidpointP012Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP012Factor2559
      batchC05119PlusMidpointP012Center2559)
  rw [batchC05119PlusMidpointP012RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP012Factor2559 * embedPair2542
        batchC05119PlusMidpointP012Center2559)
    (embedPair2542 batchC05119PlusMidpointP012Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP012DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP012Factor2559,
      batchC05119PlusMidpointP012Error2559, rounding2542,
      batchC05119PlusMidpointP012Radius2559]

theorem batchC05119PlusMidpointP012DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP012Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP012RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP012Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP012Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP012Rounded2559]

def batchC05119PlusMidpointP013Rounded2559 : RatPair2542 :=
  ((((-129229774835529403679) : ℚ) /
        1267650600228229401496703205376),
    (((-6662067346755160977) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP013Radius2559 : ℝ := ((12222137704973917 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP013RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP013Factor2559
        batchC05119PlusMidpointP013Center2559) =
        batchC05119PlusMidpointP013Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP013RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP013Rounded2559‖ ≤
          batchC05119PlusMidpointP013Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP013Factor2559
      batchC05119PlusMidpointP013Center2559)
  rw [batchC05119PlusMidpointP013RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP013Factor2559 * embedPair2542
        batchC05119PlusMidpointP013Center2559)
    (embedPair2542 batchC05119PlusMidpointP013Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP013DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP013Factor2559,
      batchC05119PlusMidpointP013Error2559, rounding2542,
      batchC05119PlusMidpointP013Radius2559]

theorem batchC05119PlusMidpointP013DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP013Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP013RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP013Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP013Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP013Rounded2559]

def batchC05119PlusMidpointP014Rounded2559 : RatPair2542 :=
  ((((-168080548783185617777) : ℚ) /
        1267650600228229401496703205376),
    (((-1067259108288674215) : ℚ) /
        158456325028528675187087900672))

noncomputable def batchC05119PlusMidpointP014Radius2559 : ℝ := ((7942199100551321 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119PlusMidpointP014RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP014Factor2559
        batchC05119PlusMidpointP014Center2559) =
        batchC05119PlusMidpointP014Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP014RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP014Rounded2559‖ ≤
          batchC05119PlusMidpointP014Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP014Factor2559
      batchC05119PlusMidpointP014Center2559)
  rw [batchC05119PlusMidpointP014RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP014Factor2559 * embedPair2542
        batchC05119PlusMidpointP014Center2559)
    (embedPair2542 batchC05119PlusMidpointP014Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP014DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP014Factor2559,
      batchC05119PlusMidpointP014Error2559, rounding2542,
      batchC05119PlusMidpointP014Radius2559]

theorem batchC05119PlusMidpointP014DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP014Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP014RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP014Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP014Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP014Rounded2559]

def batchC05119PlusMidpointP015Rounded2559 : RatPair2542 :=
  ((((-199064889149410510645) : ℚ) /
        1267650600228229401496703205376),
    (((-1263389363508690609) : ℚ) /
        158456325028528675187087900672))

noncomputable def batchC05119PlusMidpointP015Radius2559 : ℝ := ((18811784066313875 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP015RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP015Factor2559
        batchC05119PlusMidpointP015Center2559) =
        batchC05119PlusMidpointP015Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP015RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP015Rounded2559‖ ≤
          batchC05119PlusMidpointP015Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP015Factor2559
      batchC05119PlusMidpointP015Center2559)
  rw [batchC05119PlusMidpointP015RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP015Factor2559 * embedPair2542
        batchC05119PlusMidpointP015Center2559)
    (embedPair2542 batchC05119PlusMidpointP015Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP015DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP015Factor2559,
      batchC05119PlusMidpointP015Error2559, rounding2542,
      batchC05119PlusMidpointP015Radius2559]

theorem batchC05119PlusMidpointP015DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP015Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP015RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP015Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP015Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP015Rounded2559]

def batchC05119PlusMidpointP016Rounded2559 : RatPair2542 :=
  ((((-55772940637700088551) : ℚ) /
        316912650057057350374175801344),
    (((-11368777858395495983) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP016Radius2559 : ℝ := ((2635743859691231 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC05119PlusMidpointP016RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP016Factor2559
        batchC05119PlusMidpointP016Center2559) =
        batchC05119PlusMidpointP016Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP016RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP016Rounded2559‖ ≤
          batchC05119PlusMidpointP016Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP016Factor2559
      batchC05119PlusMidpointP016Center2559)
  rw [batchC05119PlusMidpointP016RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP016Factor2559 * embedPair2542
        batchC05119PlusMidpointP016Center2559)
    (embedPair2542 batchC05119PlusMidpointP016Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP016DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP016Factor2559,
      batchC05119PlusMidpointP016Error2559, rounding2542,
      batchC05119PlusMidpointP016Radius2559]

theorem batchC05119PlusMidpointP016DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP016Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP016RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP016Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP016Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP016Rounded2559]

def batchC05119PlusMidpointP017Rounded2559 : RatPair2542 :=
  ((((-68420421411826435151) : ℚ) /
        316912650057057350374175801344),
    (((-14151959878563223789) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP017Radius2559 : ℝ := ((12942995242491967 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119PlusMidpointP017RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP017Factor2559
        batchC05119PlusMidpointP017Center2559) =
        batchC05119PlusMidpointP017Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP017RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP017Rounded2559‖ ≤
          batchC05119PlusMidpointP017Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP017Factor2559
      batchC05119PlusMidpointP017Center2559)
  rw [batchC05119PlusMidpointP017RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP017Factor2559 * embedPair2542
        batchC05119PlusMidpointP017Center2559)
    (embedPair2542 batchC05119PlusMidpointP017Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP017DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP017Factor2559,
      batchC05119PlusMidpointP017Error2559, rounding2542,
      batchC05119PlusMidpointP017Radius2559]

theorem batchC05119PlusMidpointP017DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP017Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP017RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP017Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP017Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP017Rounded2559]

def batchC05119PlusMidpointP018Rounded2559 : RatPair2542 :=
  ((((-294156232294050812541) : ℚ) /
        1267650600228229401496703205376),
    (((-7663114112441634059) : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05119PlusMidpointP018Radius2559 : ℝ := ((6958265178160289 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05119PlusMidpointP018RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP018Factor2559
        batchC05119PlusMidpointP018Center2559) =
        batchC05119PlusMidpointP018Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP018RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP018Rounded2559‖ ≤
          batchC05119PlusMidpointP018Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP018Factor2559
      batchC05119PlusMidpointP018Center2559)
  rw [batchC05119PlusMidpointP018RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP018Factor2559 * embedPair2542
        batchC05119PlusMidpointP018Center2559)
    (embedPair2542 batchC05119PlusMidpointP018Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP018DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP018Factor2559,
      batchC05119PlusMidpointP018Error2559, rounding2542,
      batchC05119PlusMidpointP018Radius2559]

theorem batchC05119PlusMidpointP018DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP018Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP018RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP018Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP018Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP018Rounded2559]

def batchC05119PlusMidpointP019Rounded2559 : RatPair2542 :=
  ((((-83258578049050380147) : ℚ) /
        316912650057057350374175801344),
    (((-17629867734589877665) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP019Radius2559 : ℝ := ((31537094891650129 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP019RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP019Factor2559
        batchC05119PlusMidpointP019Center2559) =
        batchC05119PlusMidpointP019Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP019RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP019Rounded2559‖ ≤
          batchC05119PlusMidpointP019Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP019Factor2559
      batchC05119PlusMidpointP019Center2559)
  rw [batchC05119PlusMidpointP019RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP019Factor2559 * embedPair2542
        batchC05119PlusMidpointP019Center2559)
    (embedPair2542 batchC05119PlusMidpointP019Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP019DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP019Factor2559,
      batchC05119PlusMidpointP019Error2559, rounding2542,
      batchC05119PlusMidpointP019Radius2559]

theorem batchC05119PlusMidpointP019DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP019Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP019RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP019Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP019Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP019Rounded2559]

def batchC05119PlusMidpointP020Rounded2559 : RatPair2542 :=
  ((((-189025057303334293291) : ℚ) /
        633825300114114700748351602688),
    (((-20414826289757369889) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP020Radius2559 : ℝ := ((35836813814868405 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP020RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP020Factor2559
        batchC05119PlusMidpointP020Center2559) =
        batchC05119PlusMidpointP020Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP020RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP020Rounded2559‖ ≤
          batchC05119PlusMidpointP020Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP020Factor2559
      batchC05119PlusMidpointP020Center2559)
  rw [batchC05119PlusMidpointP020RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP020Factor2559 * embedPair2542
        batchC05119PlusMidpointP020Center2559)
    (embedPair2542 batchC05119PlusMidpointP020Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP020DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP020Factor2559,
      batchC05119PlusMidpointP020Error2559, rounding2542,
      batchC05119PlusMidpointP020Radius2559]

theorem batchC05119PlusMidpointP020DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP020Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP020RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP020Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP020Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP020Rounded2559]

def batchC05119PlusMidpointP021Rounded2559 : RatPair2542 :=
  ((((-417801127040212980087) : ℚ) /
        1267650600228229401496703205376),
    (((-22975654302588725451) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP021Radius2559 : ℝ := ((39643126884540141 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP021RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP021Factor2559
        batchC05119PlusMidpointP021Center2559) =
        batchC05119PlusMidpointP021Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP021RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP021Rounded2559‖ ≤
          batchC05119PlusMidpointP021Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP021Factor2559
      batchC05119PlusMidpointP021Center2559)
  rw [batchC05119PlusMidpointP021RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP021Factor2559 * embedPair2542
        batchC05119PlusMidpointP021Center2559)
    (embedPair2542 batchC05119PlusMidpointP021Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP021DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP021Factor2559,
      batchC05119PlusMidpointP021Error2559, rounding2542,
      batchC05119PlusMidpointP021Radius2559]

theorem batchC05119PlusMidpointP021DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP021Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP021RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP021Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP021Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP021Rounded2559]

def batchC05119PlusMidpointP022Rounded2559 : RatPair2542 :=
  ((((-438915514999415869391) : ℚ) /
        1267650600228229401496703205376),
    (((-24373566294243129135) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP022Radius2559 : ℝ := ((41668431869067903 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP022RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP022Factor2559
        batchC05119PlusMidpointP022Center2559) =
        batchC05119PlusMidpointP022Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP022RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP022Rounded2559‖ ≤
          batchC05119PlusMidpointP022Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP022Factor2559
      batchC05119PlusMidpointP022Center2559)
  rw [batchC05119PlusMidpointP022RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP022Factor2559 * embedPair2542
        batchC05119PlusMidpointP022Center2559)
    (embedPair2542 batchC05119PlusMidpointP022Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP022DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP022Factor2559,
      batchC05119PlusMidpointP022Error2559, rounding2542,
      batchC05119PlusMidpointP022Radius2559]

theorem batchC05119PlusMidpointP022DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP022Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP022RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP022Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP022Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP022Rounded2559]

def batchC05119PlusMidpointP023Rounded2559 : RatPair2542 :=
  ((((-62837918632044822619) : ℚ) /
        158456325028528675187087900672),
    (((-14375332182251210463) : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05119PlusMidpointP023Radius2559 : ℝ := ((47801421728456613 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP023RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP023Factor2559
        batchC05119PlusMidpointP023Center2559) =
        batchC05119PlusMidpointP023Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP023RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP023Rounded2559‖ ≤
          batchC05119PlusMidpointP023Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP023Factor2559
      batchC05119PlusMidpointP023Center2559)
  rw [batchC05119PlusMidpointP023RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP023Factor2559 * embedPair2542
        batchC05119PlusMidpointP023Center2559)
    (embedPair2542 batchC05119PlusMidpointP023Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP023DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP023Factor2559,
      batchC05119PlusMidpointP023Error2559, rounding2542,
      batchC05119PlusMidpointP023Radius2559]

theorem batchC05119PlusMidpointP023DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP023Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP023RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP023Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP023Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP023Rounded2559]

def batchC05119PlusMidpointP024Rounded2559 : RatPair2542 :=
  ((((-533466877520828668447) : ℚ) /
        1267650600228229401496703205376),
    (((-30942036089586650043) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP024Radius2559 : ℝ := ((793231022766363 : ℝ) /
        (2 * 10^40
        + 1778071482940061661655974875633165533184))

theorem batchC05119PlusMidpointP024RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP024Factor2559
        batchC05119PlusMidpointP024Center2559) =
        batchC05119PlusMidpointP024Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP024RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP024Rounded2559‖ ≤
          batchC05119PlusMidpointP024Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP024Factor2559
      batchC05119PlusMidpointP024Center2559)
  rw [batchC05119PlusMidpointP024RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP024Factor2559 * embedPair2542
        batchC05119PlusMidpointP024Center2559)
    (embedPair2542 batchC05119PlusMidpointP024Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP024DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP024Factor2559,
      batchC05119PlusMidpointP024Error2559, rounding2542,
      batchC05119PlusMidpointP024Radius2559]

theorem batchC05119PlusMidpointP024DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP024Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP024RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP024Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP024Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP024Rounded2559]

def batchC05119PlusMidpointP025Rounded2559 : RatPair2542 :=
  ((((-17916485924935400725) : ℚ) /
        39614081257132168796771975168),
    (((-16928416668871882329) : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05119PlusMidpointP025Radius2559 : ℝ := ((54616147744855189 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP025RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP025Factor2559
        batchC05119PlusMidpointP025Center2559) =
        batchC05119PlusMidpointP025Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP025RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP025Rounded2559‖ ≤
          batchC05119PlusMidpointP025Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP025Factor2559
      batchC05119PlusMidpointP025Center2559)
  rw [batchC05119PlusMidpointP025RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP025Factor2559 * embedPair2542
        batchC05119PlusMidpointP025Center2559)
    (embedPair2542 batchC05119PlusMidpointP025Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP025DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP025Factor2559,
      batchC05119PlusMidpointP025Error2559, rounding2542,
      batchC05119PlusMidpointP025Radius2559]

theorem batchC05119PlusMidpointP025DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP025Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP025RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP025Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP025Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP025Rounded2559]

def batchC05119PlusMidpointP026Rounded2559 : RatPair2542 :=
  ((((-615544534469100603829) : ℚ) /
        1267650600228229401496703205376),
    (((-37034473926654740555) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP026Radius2559 : ℝ := ((29350805287237851 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119PlusMidpointP026RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP026Factor2559
        batchC05119PlusMidpointP026Center2559) =
        batchC05119PlusMidpointP026Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP026RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP026Rounded2559‖ ≤
          batchC05119PlusMidpointP026Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP026Factor2559
      batchC05119PlusMidpointP026Center2559)
  rw [batchC05119PlusMidpointP026RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP026Factor2559 * embedPair2542
        batchC05119PlusMidpointP026Center2559)
    (embedPair2542 batchC05119PlusMidpointP026Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP026DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP026Factor2559,
      batchC05119PlusMidpointP026Error2559, rounding2542,
      batchC05119PlusMidpointP026Radius2559]

theorem batchC05119PlusMidpointP026DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP026Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP026RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP026Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP026Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP026Rounded2559]

def batchC05119PlusMidpointP027Rounded2559 : RatPair2542 :=
  ((((-84887821864139210491) : ℚ) /
        158456325028528675187087900672),
    (((-41988813293428170419) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP027Radius2559 : ℝ := ((64868447477782239 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP027RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP027Factor2559
        batchC05119PlusMidpointP027Center2559) =
        batchC05119PlusMidpointP027Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP027RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP027Rounded2559‖ ≤
          batchC05119PlusMidpointP027Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP027Factor2559
      batchC05119PlusMidpointP027Center2559)
  rw [batchC05119PlusMidpointP027RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP027Factor2559 * embedPair2542
        batchC05119PlusMidpointP027Center2559)
    (embedPair2542 batchC05119PlusMidpointP027Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP027DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP027Factor2559,
      batchC05119PlusMidpointP027Error2559, rounding2542,
      batchC05119PlusMidpointP027Radius2559]

theorem batchC05119PlusMidpointP027DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP027Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP027RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP027Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP027Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP027Rounded2559]

def batchC05119PlusMidpointP028Rounded2559 : RatPair2542 :=
  ((((-44070418092728592457) : ℚ) /
        79228162514264337593543950336),
    (((-44074929043046170739) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119PlusMidpointP028Radius2559 : ℝ := ((67398949321974451 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP028RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP028Factor2559
        batchC05119PlusMidpointP028Center2559) =
        batchC05119PlusMidpointP028Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP028RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP028Rounded2559‖ ≤
          batchC05119PlusMidpointP028Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP028Factor2559
      batchC05119PlusMidpointP028Center2559)
  rw [batchC05119PlusMidpointP028RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP028Factor2559 * embedPair2542
        batchC05119PlusMidpointP028Center2559)
    (embedPair2542 batchC05119PlusMidpointP028Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP028DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP028Factor2559,
      batchC05119PlusMidpointP028Error2559, rounding2542,
      batchC05119PlusMidpointP028Radius2559]

theorem batchC05119PlusMidpointP028DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP028Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP028RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP028Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP028Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP028Rounded2559]

def batchC05119PlusMidpointP029Rounded2559 : RatPair2542 :=
  ((((-745683670130948457301) : ℚ) /
        1267650600228229401496703205376),
    (((-23695510676650554379) : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05119PlusMidpointP029Radius2559 : ℝ := ((71348768808934797 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119PlusMidpointP029RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119PlusMidpointP029Factor2559
        batchC05119PlusMidpointP029Center2559) =
        batchC05119PlusMidpointP029Rounded2559 := by
  cbv

theorem batchC05119PlusMidpointP029RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05119PlusMidpointPosition2559 -
      embedPair2542 batchC05119PlusMidpointP029Rounded2559‖ ≤
          batchC05119PlusMidpointP029Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119PlusMidpointP029Factor2559
      batchC05119PlusMidpointP029Center2559)
  rw [batchC05119PlusMidpointP029RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP029Factor2559 * embedPair2542
        batchC05119PlusMidpointP029Center2559)
    (embedPair2542 batchC05119PlusMidpointP029Rounded2559)).trans (add_le_add
        batchC05119PlusMidpointP029DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119PlusMidpointP029Factor2559,
      batchC05119PlusMidpointP029Error2559, rounding2542,
      batchC05119PlusMidpointP029Radius2559]

theorem batchC05119PlusMidpointP029DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05119PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05119PlusMidpointPosition2559)
    (embedPair2542 batchC05119PlusMidpointP029Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119PlusMidpointP029RoundedError2559
      (embedPair_magnitude2542
      batchC05119PlusMidpointP029Rounded2559))
  apply h'.trans
  norm_num [batchC05119PlusMidpointP029Radius2559, pairMagnitude2542,
      batchC05119PlusMidpointP029Rounded2559]

noncomputable def batchC05119PlusSignedMidpointValue2559 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchC05119PlusMidpointP000Rounded2559
  | 1 => embedPair2542 batchC05119PlusMidpointP001Rounded2559
  | 2 => embedPair2542 batchC05119PlusMidpointP002Rounded2559
  | 3 => embedPair2542 batchC05119PlusMidpointP003Rounded2559
  | 4 => embedPair2542 batchC05119PlusMidpointP004Rounded2559
  | 5 => embedPair2542 batchC05119PlusMidpointP005Rounded2559
  | 6 => embedPair2542 batchC05119PlusMidpointP006Rounded2559
  | 7 => embedPair2542 batchC05119PlusMidpointP007Rounded2559
  | 8 => embedPair2542 batchC05119PlusMidpointP008Rounded2559
  | 9 => embedPair2542 batchC05119PlusMidpointP009Rounded2559
  | 10 => embedPair2542 batchC05119PlusMidpointP010Rounded2559
  | 11 => embedPair2542 batchC05119PlusMidpointP011Rounded2559
  | 12 => embedPair2542 batchC05119PlusMidpointP012Rounded2559
  | 13 => embedPair2542 batchC05119PlusMidpointP013Rounded2559
  | 14 => embedPair2542 batchC05119PlusMidpointP014Rounded2559
  | 15 => embedPair2542 batchC05119PlusMidpointP015Rounded2559
  | 16 => embedPair2542 batchC05119PlusMidpointP016Rounded2559
  | 17 => embedPair2542 batchC05119PlusMidpointP017Rounded2559
  | 18 => embedPair2542 batchC05119PlusMidpointP018Rounded2559
  | 19 => embedPair2542 batchC05119PlusMidpointP019Rounded2559
  | 20 => embedPair2542 batchC05119PlusMidpointP020Rounded2559
  | 21 => embedPair2542 batchC05119PlusMidpointP021Rounded2559
  | 22 => embedPair2542 batchC05119PlusMidpointP022Rounded2559
  | 23 => embedPair2542 batchC05119PlusMidpointP023Rounded2559
  | 24 => embedPair2542 batchC05119PlusMidpointP024Rounded2559
  | 25 => embedPair2542 batchC05119PlusMidpointP025Rounded2559
  | 26 => embedPair2542 batchC05119PlusMidpointP026Rounded2559
  | 27 => embedPair2542 batchC05119PlusMidpointP027Rounded2559
  | 28 => embedPair2542 batchC05119PlusMidpointP028Rounded2559
  | 29 => embedPair2542 batchC05119PlusMidpointP029Rounded2559
  | _ => 0

noncomputable def batchC05119PlusSignedMidpointError2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05119PlusMidpointP000Radius2559
  | 1 => batchC05119PlusMidpointP001Radius2559
  | 2 => batchC05119PlusMidpointP002Radius2559
  | 3 => batchC05119PlusMidpointP003Radius2559
  | 4 => batchC05119PlusMidpointP004Radius2559
  | 5 => batchC05119PlusMidpointP005Radius2559
  | 6 => batchC05119PlusMidpointP006Radius2559
  | 7 => batchC05119PlusMidpointP007Radius2559
  | 8 => batchC05119PlusMidpointP008Radius2559
  | 9 => batchC05119PlusMidpointP009Radius2559
  | 10 => batchC05119PlusMidpointP010Radius2559
  | 11 => batchC05119PlusMidpointP011Radius2559
  | 12 => batchC05119PlusMidpointP012Radius2559
  | 13 => batchC05119PlusMidpointP013Radius2559
  | 14 => batchC05119PlusMidpointP014Radius2559
  | 15 => batchC05119PlusMidpointP015Radius2559
  | 16 => batchC05119PlusMidpointP016Radius2559
  | 17 => batchC05119PlusMidpointP017Radius2559
  | 18 => batchC05119PlusMidpointP018Radius2559
  | 19 => batchC05119PlusMidpointP019Radius2559
  | 20 => batchC05119PlusMidpointP020Radius2559
  | 21 => batchC05119PlusMidpointP021Radius2559
  | 22 => batchC05119PlusMidpointP022Radius2559
  | 23 => batchC05119PlusMidpointP023Radius2559
  | 24 => batchC05119PlusMidpointP024Radius2559
  | 25 => batchC05119PlusMidpointP025Radius2559
  | 26 => batchC05119PlusMidpointP026Radius2559
  | 27 => batchC05119PlusMidpointP027Radius2559
  | 28 => batchC05119PlusMidpointP028Radius2559
  | 29 => batchC05119PlusMidpointP029Radius2559
  | _ => 0

theorem batchC05119PlusSignedMidpointExpError2559 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC05119PlusMidpointPosition2559 -
        batchC05119PlusSignedMidpointValue2559 i‖ ≤ batchC05119PlusSignedMidpointError2559 i := by
  fin_cases i
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP000RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP001RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP002RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP003RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP004RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP005RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP006RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP007RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP008RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP009RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP010RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP011RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP012RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP013RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP014RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP015RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP016RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP017RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP018RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP019RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP020RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP021RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP022RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP023RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP024RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP025RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP026RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP027RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP028RoundedError2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP029RoundedError2559

theorem batchC05119PlusSignedMidpointUnitNorm2559 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC05119PlusMidpointPosition2559‖ ≤ 1 :=
        by
  fin_cases i
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP000DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP001DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP002DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP003DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP004DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP005DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP006DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP007DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP008DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP009DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP010DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP011DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP012DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP013DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP014DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP015DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP016DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP017DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP018DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP019DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP020DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP021DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP022DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP023DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP024DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP025DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP026DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP027DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP028DerivativeNorm2559
  · simpa only [batchC05119PlusSignedMidpointValue2559, batchC05119PlusSignedMidpointError2559]
      using
      batchC05119PlusMidpointP029DerivativeNorm2559

noncomputable def batchC05119PlusSignedMidpointSum2559 : ℂ := ⟨(((-(((21194439503 * 10^40
        + 3878658114213823590938459696395451527690) * 10^40
        + 88065552112843357367886866263295029946) * 10^40
        + 912683315242595260792559664483351386957)) : ℝ) /
        (((676921 * 10^40
        + 3120412145653267612754255575447842863953) * 10^40
        + 5542396854748036636099153022598281812499) * 10^40
        + 3751490268451683933401113623918903558144)),
    (((-(((30286105215 * 10^40
        + 8926889795811375240743446276068218701158) * 10^40
        + 7443144749992239490622308274556615746784) * 10^40
        + 7435892265204404499772921398054492777527)) : ℝ) /
        (((21661481 * 10^40
        + 9853188660904563608136178414330971646513) * 10^40
        + 7356699351937172355172896723145017999980) * 10^40
        + 47688590453885868835635965404913860608))⟩

noncomputable def batchC05119PlusSignedMidpointUpper2559 : ℝ := ((313412509367 : ℝ) /
        10000000)

theorem batchC05119PlusSignedMidpointSum_eq2559 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchC05119PlusSignedMidpointValue2559 i) =
      batchC05119PlusSignedMidpointSum2559 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
        batchC05119PlusSignedMidpointValue2559,
      batchC05119PlusSignedMidpointSum2559, embedPair2542, batchC05119PlusMidpointP000Rounded2559,
      batchC05119PlusMidpointP001Rounded2559,
      batchC05119PlusMidpointP002Rounded2559,
      batchC05119PlusMidpointP003Rounded2559,
      batchC05119PlusMidpointP004Rounded2559,
      batchC05119PlusMidpointP005Rounded2559,
      batchC05119PlusMidpointP006Rounded2559,
      batchC05119PlusMidpointP007Rounded2559,
      batchC05119PlusMidpointP008Rounded2559,
      batchC05119PlusMidpointP009Rounded2559,
      batchC05119PlusMidpointP010Rounded2559,
      batchC05119PlusMidpointP011Rounded2559,
      batchC05119PlusMidpointP012Rounded2559,
      batchC05119PlusMidpointP013Rounded2559,
      batchC05119PlusMidpointP014Rounded2559,
      batchC05119PlusMidpointP015Rounded2559,
      batchC05119PlusMidpointP016Rounded2559,
      batchC05119PlusMidpointP017Rounded2559,
      batchC05119PlusMidpointP018Rounded2559,
      batchC05119PlusMidpointP019Rounded2559,
      batchC05119PlusMidpointP020Rounded2559,
      batchC05119PlusMidpointP021Rounded2559,
      batchC05119PlusMidpointP022Rounded2559,
      batchC05119PlusMidpointP023Rounded2559,
      batchC05119PlusMidpointP024Rounded2559,
      batchC05119PlusMidpointP025Rounded2559,
      batchC05119PlusMidpointP026Rounded2559,
      batchC05119PlusMidpointP027Rounded2559,
      batchC05119PlusMidpointP028Rounded2559,
      batchC05119PlusMidpointP029Rounded2559, Complex.mul_re, Complex.mul_im]

theorem batchC05119PlusSignedMidpointSum_norm2559 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC05119PlusSignedMidpointValue2559 i‖ ≤
        ((156706254683 : ℝ)
        /
        5000000) := by
  rw [batchC05119PlusSignedMidpointSum_eq2559]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchC05119PlusSignedMidpointSum2559]

theorem batchC05119PlusSignedMidpointCharge2559 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchC05119PlusSignedMidpointError2559 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
      batchC05119PlusSignedMidpointError2559,
      batchC05119PlusMidpointP000Radius2559,
      batchC05119PlusMidpointP001Radius2559,
      batchC05119PlusMidpointP002Radius2559,
      batchC05119PlusMidpointP003Radius2559,
      batchC05119PlusMidpointP004Radius2559,
      batchC05119PlusMidpointP005Radius2559,
      batchC05119PlusMidpointP006Radius2559,
      batchC05119PlusMidpointP007Radius2559,
      batchC05119PlusMidpointP008Radius2559,
      batchC05119PlusMidpointP009Radius2559,
      batchC05119PlusMidpointP010Radius2559,
      batchC05119PlusMidpointP011Radius2559,
      batchC05119PlusMidpointP012Radius2559,
      batchC05119PlusMidpointP013Radius2559,
      batchC05119PlusMidpointP014Radius2559,
      batchC05119PlusMidpointP015Radius2559,
      batchC05119PlusMidpointP016Radius2559,
      batchC05119PlusMidpointP017Radius2559,
      batchC05119PlusMidpointP018Radius2559,
      batchC05119PlusMidpointP019Radius2559,
      batchC05119PlusMidpointP020Radius2559,
      batchC05119PlusMidpointP021Radius2559,
      batchC05119PlusMidpointP022Radius2559,
      batchC05119PlusMidpointP023Radius2559,
      batchC05119PlusMidpointP024Radius2559,
      batchC05119PlusMidpointP025Radius2559,
      batchC05119PlusMidpointP026Radius2559,
      batchC05119PlusMidpointP027Radius2559,
      batchC05119PlusMidpointP028Radius2559,
      batchC05119PlusMidpointP029Radius2559]

theorem batchC05119PlusSignedMidpointUpper_le2559 :
    signedJetUpper2539 2 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchC05119PlusMidpointPosition2559 ≤
          batchC05119PlusSignedMidpointUpper2559 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC05119PlusMidpointPosition2559‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC05119PlusSignedMidpointValue2559 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchC05119PlusSignedMidpointError2559 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (batchC05119PlusSignedMidpointExpError2559 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC05119PlusMidpointPosition2559‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchC05119PlusSignedMidpointUnitNorm2559 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC05119PlusMidpointPosition2559‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchC05119PlusSignedMidpointUpper2559
  linarith [batchC05119PlusSignedMidpointSum_norm2559, batchC05119PlusSignedMidpointCharge2559]

theorem batchC05119PlusPhysicalSecond2559 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        batchC05119PlusMidpointPosition2559‖ ≤
      batchC05119PlusSignedMidpointUpper2559 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchC05119PlusMidpointPosition2559
  exact h.trans batchC05119PlusSignedMidpointUpper_le2559

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05119PlusSignedMidpointExpError2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusSignedMidpointSum_eq2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusSignedMidpointCharge2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusSignedMidpointUpper_le2559
#print axioms ConnesWeilRH.Dev.batchC05119PlusPhysicalSecond2559
