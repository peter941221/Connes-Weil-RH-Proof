import ConnesWeilRH.Dev.C1RouteABatchC05119MinusMidpoint2559

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem batchC05119MinusMidpoint_triangle2559 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def batchC05119MinusMidpointP000Rounded2559 : RatPair2542 :=
  ((((-183940495763945674589) : ℚ) /
        1267650600228229401496703205376),
    (((-8645616812935547) : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05119MinusMidpointP000Radius2559 : ℝ := ((17350391795379231 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119MinusMidpointP000RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP000Factor2559
        batchC05119MinusMidpointP000Center2559) =
        batchC05119MinusMidpointP000Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP000RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP000Rounded2559‖ ≤
          batchC05119MinusMidpointP000Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP000Factor2559
      batchC05119MinusMidpointP000Center2559)
  rw [batchC05119MinusMidpointP000RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP000Factor2559 * embedPair2542
        batchC05119MinusMidpointP000Center2559)
    (embedPair2542 batchC05119MinusMidpointP000Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP000DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP000Factor2559,
      batchC05119MinusMidpointP000Error2559, rounding2542,
      batchC05119MinusMidpointP000Radius2559]

theorem batchC05119MinusMidpointP000DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP000Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP000RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP000Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP000Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP000Rounded2559]

def batchC05119MinusMidpointP001Rounded2559 : RatPair2542 :=
  ((((-91737925408470581679) : ℚ) /
        633825300114114700748351602688),
    ((8884797733023975 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05119MinusMidpointP001Radius2559 : ℝ := ((17309709757978755 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119MinusMidpointP001RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP001Factor2559
        batchC05119MinusMidpointP001Center2559) =
        batchC05119MinusMidpointP001Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP001RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP001Rounded2559‖ ≤
          batchC05119MinusMidpointP001Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP001Factor2559
      batchC05119MinusMidpointP001Center2559)
  rw [batchC05119MinusMidpointP001RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP001Factor2559 * embedPair2542
        batchC05119MinusMidpointP001Center2559)
    (embedPair2542 batchC05119MinusMidpointP001Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP001DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP001Factor2559,
      batchC05119MinusMidpointP001Error2559, rounding2542,
      batchC05119MinusMidpointP001Radius2559]

theorem batchC05119MinusMidpointP001DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP001Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP001RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP001Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP001Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP001Rounded2559]

def batchC05119MinusMidpointP002Rounded2559 : RatPair2542 :=
  ((((-183235387823346688305) : ℚ) /
        1267650600228229401496703205376),
    (((-4489280462481769) : ℚ) /
        158456325028528675187087900672))

noncomputable def batchC05119MinusMidpointP002Radius2559 : ℝ := ((17288655993512839 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119MinusMidpointP002RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP002Factor2559
        batchC05119MinusMidpointP002Center2559) =
        batchC05119MinusMidpointP002Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP002RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP002Rounded2559‖ ≤
          batchC05119MinusMidpointP002Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP002Factor2559
      batchC05119MinusMidpointP002Center2559)
  rw [batchC05119MinusMidpointP002RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP002Factor2559 * embedPair2542
        batchC05119MinusMidpointP002Center2559)
    (embedPair2542 batchC05119MinusMidpointP002Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP002DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP002Factor2559,
      batchC05119MinusMidpointP002Error2559, rounding2542,
      batchC05119MinusMidpointP002Radius2559]

theorem batchC05119MinusMidpointP002DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP002Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP002RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP002Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP002Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP002Rounded2559]

def batchC05119MinusMidpointP003Rounded2559 : RatPair2542 :=
  ((((-183100946266297838907) : ℚ) /
        1267650600228229401496703205376),
    (((-46058810039771545) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP003Radius2559 : ℝ := ((2159610618419887 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC05119MinusMidpointP003RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP003Factor2559
        batchC05119MinusMidpointP003Center2559) =
        batchC05119MinusMidpointP003Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP003RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP003Rounded2559‖ ≤
          batchC05119MinusMidpointP003Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP003Factor2559
      batchC05119MinusMidpointP003Center2559)
  rw [batchC05119MinusMidpointP003RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP003Factor2559 * embedPair2542
        batchC05119MinusMidpointP003Center2559)
    (embedPair2542 batchC05119MinusMidpointP003Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP003DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP003Factor2559,
      batchC05119MinusMidpointP003Error2559, rounding2542,
      batchC05119MinusMidpointP003Radius2559]

theorem batchC05119MinusMidpointP003DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP003Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP003RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP003Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP003Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP003Rounded2559]

def batchC05119MinusMidpointP004Rounded2559 : RatPair2542 :=
  ((((-91510528552314328875) : ℚ) /
        633825300114114700748351602688),
    ((52087009534365069 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP004Radius2559 : ℝ := ((17269890242354937 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119MinusMidpointP004RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP004Factor2559
        batchC05119MinusMidpointP004Center2559) =
        batchC05119MinusMidpointP004Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP004RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP004Rounded2559‖ ≤
          batchC05119MinusMidpointP004Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP004Factor2559
      batchC05119MinusMidpointP004Center2559)
  rw [batchC05119MinusMidpointP004RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP004Factor2559 * embedPair2542
        batchC05119MinusMidpointP004Center2559)
    (embedPair2542 batchC05119MinusMidpointP004Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP004DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP004Factor2559,
      batchC05119MinusMidpointP004Error2559, rounding2542,
      batchC05119MinusMidpointP004Radius2559]

theorem batchC05119MinusMidpointP004DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP004Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP004RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP004Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP004Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP004Rounded2559]

def batchC05119MinusMidpointP005Rounded2559 : RatPair2542 :=
  ((((-864657634398094865) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusMidpointP005Radius2559 : ℝ := ((79884661840319 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119MinusMidpointP005RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP005Factor2559
        batchC05119MinusMidpointP005Center2559) =
        batchC05119MinusMidpointP005Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP005RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP005Rounded2559‖ ≤
          batchC05119MinusMidpointP005Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP005Factor2559
      batchC05119MinusMidpointP005Center2559)
  rw [batchC05119MinusMidpointP005RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP005Factor2559 * embedPair2542
        batchC05119MinusMidpointP005Center2559)
    (embedPair2542 batchC05119MinusMidpointP005Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP005DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP005Factor2559,
      batchC05119MinusMidpointP005Error2559, rounding2542,
      batchC05119MinusMidpointP005Radius2559]

theorem batchC05119MinusMidpointP005DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP005Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP005RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP005Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP005Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP005Rounded2559]

def batchC05119MinusMidpointP006Rounded2559 : RatPair2542 :=
  ((((-103898400115067305) : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusMidpointP006Radius2559 : ℝ := ((19769128466637 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119MinusMidpointP006RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP006Factor2559
        batchC05119MinusMidpointP006Center2559) =
        batchC05119MinusMidpointP006Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP006RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP006Rounded2559‖ ≤
          batchC05119MinusMidpointP006Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP006Factor2559
      batchC05119MinusMidpointP006Center2559)
  rw [batchC05119MinusMidpointP006RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP006Factor2559 * embedPair2542
        batchC05119MinusMidpointP006Center2559)
    (embedPair2542 batchC05119MinusMidpointP006Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP006DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP006Factor2559,
      batchC05119MinusMidpointP006Error2559, rounding2542,
      batchC05119MinusMidpointP006Radius2559]

theorem batchC05119MinusMidpointP006DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP006Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP006RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP006Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP006Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP006Rounded2559]

def batchC05119MinusMidpointP007Rounded2559 : RatPair2542 :=
  ((((-54061901476631533) : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def batchC05119MinusMidpointP007Radius2559 : ℝ := ((5406976782575 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05119MinusMidpointP007RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP007Factor2559
        batchC05119MinusMidpointP007Center2559) =
        batchC05119MinusMidpointP007Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP007RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP007Rounded2559‖ ≤
          batchC05119MinusMidpointP007Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP007Factor2559
      batchC05119MinusMidpointP007Center2559)
  rw [batchC05119MinusMidpointP007RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP007Factor2559 * embedPair2542
        batchC05119MinusMidpointP007Center2559)
    (embedPair2542 batchC05119MinusMidpointP007Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP007DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP007Factor2559,
      batchC05119MinusMidpointP007Error2559, rounding2542,
      batchC05119MinusMidpointP007Radius2559]

theorem batchC05119MinusMidpointP007DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP007Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP007RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP007Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP007Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP007Rounded2559]

def batchC05119MinusMidpointP008Rounded2559 : RatPair2542 :=
  ((((-24433951067878118749) : ℚ) /
        1267650600228229401496703205376),
    ((1442825777717264175 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP008Radius2559 : ℝ := ((2366266502585211 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119MinusMidpointP008RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP008Factor2559
        batchC05119MinusMidpointP008Center2559) =
        batchC05119MinusMidpointP008Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP008RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP008Rounded2559‖ ≤
          batchC05119MinusMidpointP008Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP008Factor2559
      batchC05119MinusMidpointP008Center2559)
  rw [batchC05119MinusMidpointP008RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP008Factor2559 * embedPair2542
        batchC05119MinusMidpointP008Center2559)
    (embedPair2542 batchC05119MinusMidpointP008Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP008DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP008Factor2559,
      batchC05119MinusMidpointP008Error2559, rounding2542,
      batchC05119MinusMidpointP008Radius2559]

theorem batchC05119MinusMidpointP008DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP008Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP008RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP008Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP008Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP008Rounded2559]

def batchC05119MinusMidpointP009Rounded2559 : RatPair2542 :=
  ((((-3323759233456253897) : ℚ) /
        79228162514264337593543950336),
    ((439798527161347041 : ℚ) /
        316912650057057350374175801344))

noncomputable def batchC05119MinusMidpointP009Radius2559 : ℝ := ((316576520179561 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem batchC05119MinusMidpointP009RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP009Factor2559
        batchC05119MinusMidpointP009Center2559) =
        batchC05119MinusMidpointP009Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP009RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP009Rounded2559‖ ≤
          batchC05119MinusMidpointP009Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP009Factor2559
      batchC05119MinusMidpointP009Center2559)
  rw [batchC05119MinusMidpointP009RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP009Factor2559 * embedPair2542
        batchC05119MinusMidpointP009Center2559)
    (embedPair2542 batchC05119MinusMidpointP009Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP009DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP009Factor2559,
      batchC05119MinusMidpointP009Error2559, rounding2542,
      batchC05119MinusMidpointP009Radius2559]

theorem batchC05119MinusMidpointP009DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP009Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP009RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP009Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP009Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP009Rounded2559]

def batchC05119MinusMidpointP010Rounded2559 : RatPair2542 :=
  ((((-9372140438565578331) : ℚ) /
        158456325028528675187087900672),
    ((872074072820880169 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05119MinusMidpointP010Radius2559 : ℝ := ((7108446678226625 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119MinusMidpointP010RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP010Factor2559
        batchC05119MinusMidpointP010Center2559) =
        batchC05119MinusMidpointP010Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP010RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP010Rounded2559‖ ≤
          batchC05119MinusMidpointP010Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP010Factor2559
      batchC05119MinusMidpointP010Center2559)
  rw [batchC05119MinusMidpointP010RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP010Factor2559 * embedPair2542
        batchC05119MinusMidpointP010Center2559)
    (embedPair2542 batchC05119MinusMidpointP010Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP010DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP010Factor2559,
      batchC05119MinusMidpointP010Error2559, rounding2542,
      batchC05119MinusMidpointP010Radius2559]

theorem batchC05119MinusMidpointP010DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP010Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP010RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP010Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP010Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP010Rounded2559]

def batchC05119MinusMidpointP011Rounded2559 : RatPair2542 :=
  ((((-91607596240301853881) : ℚ) /
        1267650600228229401496703205376),
    ((1635135729097111063 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP011Radius2559 : ℝ := ((4333994408806955 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119MinusMidpointP011RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP011Factor2559
        batchC05119MinusMidpointP011Center2559) =
        batchC05119MinusMidpointP011Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP011RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP011Rounded2559‖ ≤
          batchC05119MinusMidpointP011Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP011Factor2559
      batchC05119MinusMidpointP011Center2559)
  rw [batchC05119MinusMidpointP011RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP011Factor2559 * embedPair2542
        batchC05119MinusMidpointP011Center2559)
    (embedPair2542 batchC05119MinusMidpointP011Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP011DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP011Factor2559,
      batchC05119MinusMidpointP011Error2559, rounding2542,
      batchC05119MinusMidpointP011Radius2559]

theorem batchC05119MinusMidpointP011DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP011Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP011RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP011Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP011Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP011Rounded2559]

def batchC05119MinusMidpointP012Rounded2559 : RatPair2542 :=
  ((((-110601743460522909147) : ℚ) /
        1267650600228229401496703205376),
    ((89255691842443647 : ℚ) /
        79228162514264337593543950336))

noncomputable def batchC05119MinusMidpointP012Radius2559 : ℝ := ((2612653544312441 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05119MinusMidpointP012RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP012Factor2559
        batchC05119MinusMidpointP012Center2559) =
        batchC05119MinusMidpointP012Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP012RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP012Rounded2559‖ ≤
          batchC05119MinusMidpointP012Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP012Factor2559
      batchC05119MinusMidpointP012Center2559)
  rw [batchC05119MinusMidpointP012RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP012Factor2559 * embedPair2542
        batchC05119MinusMidpointP012Center2559)
    (embedPair2542 batchC05119MinusMidpointP012Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP012DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP012Factor2559,
      batchC05119MinusMidpointP012Error2559, rounding2542,
      batchC05119MinusMidpointP012Radius2559]

theorem batchC05119MinusMidpointP012DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP012Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP012RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP012Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP012Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP012Rounded2559]

def batchC05119MinusMidpointP013Rounded2559 : RatPair2542 :=
  ((((-129478197626521732501) : ℚ) /
        1267650600228229401496703205376),
    ((1148045373662508259 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP013Radius2559 : ℝ := ((12224067570614081 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119MinusMidpointP013RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP013Factor2559
        batchC05119MinusMidpointP013Center2559) =
        batchC05119MinusMidpointP013Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP013RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP013Rounded2559‖ ≤
          batchC05119MinusMidpointP013Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP013Factor2559
      batchC05119MinusMidpointP013Center2559)
  rw [batchC05119MinusMidpointP013RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP013Factor2559 * embedPair2542
        batchC05119MinusMidpointP013Center2559)
    (embedPair2542 batchC05119MinusMidpointP013Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP013DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP013Factor2559,
      batchC05119MinusMidpointP013Error2559, rounding2542,
      batchC05119MinusMidpointP013Radius2559]

theorem batchC05119MinusMidpointP013DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP013Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP013RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP013Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP013Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP013Rounded2559]

def batchC05119MinusMidpointP014Rounded2559 : RatPair2542 :=
  ((((-168403653973331333823) : ℚ) /
        1267650600228229401496703205376),
    ((186896281727110495 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05119MinusMidpointP014Radius2559 : ℝ := ((3971942743748627 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05119MinusMidpointP014RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP014Factor2559
        batchC05119MinusMidpointP014Center2559) =
        batchC05119MinusMidpointP014Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP014RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP014Rounded2559‖ ≤
          batchC05119MinusMidpointP014Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP014Factor2559
      batchC05119MinusMidpointP014Center2559)
  rw [batchC05119MinusMidpointP014RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP014Factor2559 * embedPair2542
        batchC05119MinusMidpointP014Center2559)
    (embedPair2542 batchC05119MinusMidpointP014Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP014DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP014Factor2559,
      batchC05119MinusMidpointP014Error2559, rounding2542,
      batchC05119MinusMidpointP014Radius2559]

theorem batchC05119MinusMidpointP014DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP014Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP014RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP014Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP014Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP014Rounded2559]

def batchC05119MinusMidpointP015Rounded2559 : RatPair2542 :=
  ((((-199447558385301084203) : ℚ) /
        1267650600228229401496703205376),
    (((-406127963062165319) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP015Radius2559 : ℝ := ((9408187995083501 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119MinusMidpointP015RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP015Factor2559
        batchC05119MinusMidpointP015Center2559) =
        batchC05119MinusMidpointP015Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP015RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP015Rounded2559‖ ≤
          batchC05119MinusMidpointP015Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP015Factor2559
      batchC05119MinusMidpointP015Center2559)
  rw [batchC05119MinusMidpointP015RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP015Factor2559 * embedPair2542
        batchC05119MinusMidpointP015Center2559)
    (embedPair2542 batchC05119MinusMidpointP015Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP015DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP015Factor2559,
      batchC05119MinusMidpointP015Error2559, rounding2542,
      batchC05119MinusMidpointP015Radius2559]

theorem batchC05119MinusMidpointP015DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP015Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP015RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP015Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP015Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP015Rounded2559]

def batchC05119MinusMidpointP016Rounded2559 : RatPair2542 :=
  ((((-55880155702662492677) : ℚ) /
        316912650057057350374175801344),
    (((-1097673722696157771) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP016Radius2559 : ℝ := ((2636440093008137 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC05119MinusMidpointP016RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP016Factor2559
        batchC05119MinusMidpointP016Center2559) =
        batchC05119MinusMidpointP016Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP016RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP016Rounded2559‖ ≤
          batchC05119MinusMidpointP016Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP016Factor2559
      batchC05119MinusMidpointP016Center2559)
  rw [batchC05119MinusMidpointP016RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP016Factor2559 * embedPair2542
        batchC05119MinusMidpointP016Center2559)
    (embedPair2542 batchC05119MinusMidpointP016Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP016DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP016Factor2559,
      batchC05119MinusMidpointP016Error2559, rounding2542,
      batchC05119MinusMidpointP016Radius2559]

theorem batchC05119MinusMidpointP016DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP016Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP016RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP016Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP016Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP016Rounded2559]

def batchC05119MinusMidpointP017Rounded2559 : RatPair2542 :=
  ((((-68551952319009991191) : ℚ) /
        316912650057057350374175801344),
    (((-2773864638270002895) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP017Radius2559 : ℝ := ((25893693689489611 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119MinusMidpointP017RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP017Factor2559
        batchC05119MinusMidpointP017Center2559) =
        batchC05119MinusMidpointP017Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP017RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP017Rounded2559‖ ≤
          batchC05119MinusMidpointP017Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP017Factor2559
      batchC05119MinusMidpointP017Center2559)
  rw [batchC05119MinusMidpointP017RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP017Factor2559 * embedPair2542
        batchC05119MinusMidpointP017Center2559)
    (embedPair2542 batchC05119MinusMidpointP017Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP017DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP017Factor2559,
      batchC05119MinusMidpointP017Error2559, rounding2542,
      batchC05119MinusMidpointP017Radius2559]

theorem batchC05119MinusMidpointP017DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP017Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP017RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP017Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP017Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP017Rounded2559]

def batchC05119MinusMidpointP018Rounded2559 : RatPair2542 :=
  ((((-36840215263819480023) : ℚ) /
        158456325028528675187087900672),
    (((-882439872900065699) : ℚ) /
        316912650057057350374175801344))

noncomputable def batchC05119MinusMidpointP018Radius2559 : ℝ := ((13920825651505617 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119MinusMidpointP018RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP018Factor2559
        batchC05119MinusMidpointP018Center2559) =
        batchC05119MinusMidpointP018Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP018RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP018Rounded2559‖ ≤
          batchC05119MinusMidpointP018Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP018Factor2559
      batchC05119MinusMidpointP018Center2559)
  rw [batchC05119MinusMidpointP018RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP018Factor2559 * embedPair2542
        batchC05119MinusMidpointP018Center2559)
    (embedPair2542 batchC05119MinusMidpointP018Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP018DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP018Factor2559,
      batchC05119MinusMidpointP018Error2559, rounding2542,
      batchC05119MinusMidpointP018Radius2559]

theorem batchC05119MinusMidpointP018DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP018Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP018RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP018Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP018Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP018Rounded2559]

def batchC05119MinusMidpointP019Rounded2559 : RatPair2542 :=
  ((((-333674555892398885997) : ℚ) /
        1267650600228229401496703205376),
    (((-5077516633308947463) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP019Radius2559 : ℝ := ((15773701178068867 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119MinusMidpointP019RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP019Factor2559
        batchC05119MinusMidpointP019Center2559) =
        batchC05119MinusMidpointP019Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP019RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP019Rounded2559‖ ≤
          batchC05119MinusMidpointP019Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP019Factor2559
      batchC05119MinusMidpointP019Center2559)
  rw [batchC05119MinusMidpointP019RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP019Factor2559 * embedPair2542
        batchC05119MinusMidpointP019Center2559)
    (embedPair2542 batchC05119MinusMidpointP019Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP019DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP019Factor2559,
      batchC05119MinusMidpointP019Error2559, rounding2542,
      batchC05119MinusMidpointP019Radius2559]

theorem batchC05119MinusMidpointP019DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP019Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP019RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP019Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP019Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP019Rounded2559]

def batchC05119MinusMidpointP020Rounded2559 : RatPair2542 :=
  ((((-378776919252039145471) : ℚ) /
        1267650600228229401496703205376),
    (((-7040872152109041585) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP020Radius2559 : ℝ := ((35849154371483411 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119MinusMidpointP020RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP020Factor2559
        batchC05119MinusMidpointP020Center2559) =
        batchC05119MinusMidpointP020Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP020RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP020Rounded2559‖ ≤
          batchC05119MinusMidpointP020Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP020Factor2559
      batchC05119MinusMidpointP020Center2559)
  rw [batchC05119MinusMidpointP020RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP020Factor2559 * embedPair2542
        batchC05119MinusMidpointP020Center2559)
    (embedPair2542 batchC05119MinusMidpointP020Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP020DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP020Factor2559,
      batchC05119MinusMidpointP020Error2559, rounding2542,
      batchC05119MinusMidpointP020Radius2559]

theorem batchC05119MinusMidpointP020DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP020Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP020RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP020Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP020Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP020Rounded2559]

def batchC05119MinusMidpointP021Rounded2559 : RatPair2542 :=
  ((((-418604373958996558163) : ℚ) /
        1267650600228229401496703205376),
    (((-8916343502464696649) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP021Radius2559 : ℝ := ((39657297370555605 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119MinusMidpointP021RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP021Factor2559
        batchC05119MinusMidpointP021Center2559) =
        batchC05119MinusMidpointP021Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP021RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP021Rounded2559‖ ≤
          batchC05119MinusMidpointP021Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP021Factor2559
      batchC05119MinusMidpointP021Center2559)
  rw [batchC05119MinusMidpointP021RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP021Factor2559 * embedPair2542
        batchC05119MinusMidpointP021Center2559)
    (embedPair2542 batchC05119MinusMidpointP021Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP021DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP021Factor2559,
      batchC05119MinusMidpointP021Error2559, rounding2542,
      batchC05119MinusMidpointP021Radius2559]

theorem batchC05119MinusMidpointP021DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP021Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP021RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP021Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP021Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP021Rounded2559]

def batchC05119MinusMidpointP022Rounded2559 : RatPair2542 :=
  ((((-219879683682105091277) : ℚ) /
        633825300114114700748351602688),
    (((-4981788185881078103) : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05119MinusMidpointP022Radius2559 : ℝ := ((41683586093847671 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05119MinusMidpointP022RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP022Factor2559
        batchC05119MinusMidpointP022Center2559) =
        batchC05119MinusMidpointP022Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP022RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP022Rounded2559‖ ≤
          batchC05119MinusMidpointP022Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP022Factor2559
      batchC05119MinusMidpointP022Center2559)
  rw [batchC05119MinusMidpointP022RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP022Factor2559 * embedPair2542
        batchC05119MinusMidpointP022Center2559)
    (embedPair2542 batchC05119MinusMidpointP022Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP022DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP022Factor2559,
      batchC05119MinusMidpointP022Error2559, rounding2542,
      batchC05119MinusMidpointP022Radius2559]

theorem batchC05119MinusMidpointP022DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP022Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP022RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP022Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP022Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP022Rounded2559]

def batchC05119MinusMidpointP023Rounded2559 : RatPair2542 :=
  ((((-251834940474035551461) : ℚ) /
        633825300114114700748351602688),
    (((-13330045471795803135) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP023Radius2559 : ℝ := ((93397640091953 : ℝ) /
        2722258935367507707706996859454145691648)

theorem batchC05119MinusMidpointP023RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP023Factor2559
        batchC05119MinusMidpointP023Center2559) =
        batchC05119MinusMidpointP023Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP023RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP023Rounded2559‖ ≤
          batchC05119MinusMidpointP023Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP023Factor2559
      batchC05119MinusMidpointP023Center2559)
  rw [batchC05119MinusMidpointP023RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP023Factor2559 * embedPair2542
        batchC05119MinusMidpointP023Center2559)
    (embedPair2542 batchC05119MinusMidpointP023Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP023DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP023Factor2559,
      batchC05119MinusMidpointP023Error2559, rounding2542,
      batchC05119MinusMidpointP023Radius2559]

theorem batchC05119MinusMidpointP023DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP023Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP023RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP023Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP023Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP023Rounded2559]

def batchC05119MinusMidpointP024Rounded2559 : RatPair2542 :=
  ((((-534492579481308767505) : ℚ) /
        1267650600228229401496703205376),
    (((-15057203438873788497) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP024Radius2559 : ℝ := ((25393215580568941 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119MinusMidpointP024RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP024Factor2559
        batchC05119MinusMidpointP024Center2559) =
        batchC05119MinusMidpointP024Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP024RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP024Rounded2559‖ ≤
          batchC05119MinusMidpointP024Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP024Factor2559
      batchC05119MinusMidpointP024Center2559)
  rw [batchC05119MinusMidpointP024RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP024Factor2559 * embedPair2542
        batchC05119MinusMidpointP024Center2559)
    (embedPair2542 batchC05119MinusMidpointP024Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP024DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP024Factor2559,
      batchC05119MinusMidpointP024Error2559, rounding2542,
      batchC05119MinusMidpointP024Radius2559]

theorem batchC05119MinusMidpointP024DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP024Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP024RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP024Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP024Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP024Rounded2559]

def batchC05119MinusMidpointP025Rounded2559 : RatPair2542 :=
  ((((-574429923105187384521) : ℚ) /
        1267650600228229401496703205376),
    (((-17390176049050181279) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP025Radius2559 : ℝ := ((13659430997976753 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05119MinusMidpointP025RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP025Factor2559
        batchC05119MinusMidpointP025Center2559) =
        batchC05119MinusMidpointP025Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP025RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP025Rounded2559‖ ≤
          batchC05119MinusMidpointP025Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP025Factor2559
      batchC05119MinusMidpointP025Center2559)
  rw [batchC05119MinusMidpointP025RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP025Factor2559 * embedPair2542
        batchC05119MinusMidpointP025Center2559)
    (embedPair2542 batchC05119MinusMidpointP025Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP025DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP025Factor2559,
      batchC05119MinusMidpointP025Error2559, rounding2542,
      batchC05119MinusMidpointP025Radius2559]

theorem batchC05119MinusMidpointP025DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP025Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP025RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP025Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP025Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP025Rounded2559]

def batchC05119MinusMidpointP026Rounded2559 : RatPair2542 :=
  ((((-616728117011192675241) : ℚ) /
        1267650600228229401496703205376),
    (((-19973470242953972879) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05119MinusMidpointP026Radius2559 : ℝ := ((29362626203609309 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119MinusMidpointP026RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP026Factor2559
        batchC05119MinusMidpointP026Center2559) =
        batchC05119MinusMidpointP026Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP026RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP026Rounded2559‖ ≤
          batchC05119MinusMidpointP026Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP026Factor2559
      batchC05119MinusMidpointP026Center2559)
  rw [batchC05119MinusMidpointP026RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP026Factor2559 * embedPair2542
        batchC05119MinusMidpointP026Center2559)
    (embedPair2542 batchC05119MinusMidpointP026Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP026DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP026Factor2559,
      batchC05119MinusMidpointP026Error2559, rounding2542,
      batchC05119MinusMidpointP026Radius2559]

theorem batchC05119MinusMidpointP026DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP026Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP026RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP026Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP026Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP026Rounded2559]

def batchC05119MinusMidpointP027Rounded2559 : RatPair2542 :=
  ((((-340204214179842058811) : ℚ) /
        633825300114114700748351602688),
    (((-3008827628061059071) : ℚ) /
        158456325028528675187087900672))

noncomputable def batchC05119MinusMidpointP027Radius2559 : ℝ := ((16223808978053165 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05119MinusMidpointP027RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP027Factor2559
        batchC05119MinusMidpointP027Center2559) =
        batchC05119MinusMidpointP027Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP027RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP027Rounded2559‖ ≤
          batchC05119MinusMidpointP027Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP027Factor2559
      batchC05119MinusMidpointP027Center2559)
  rw [batchC05119MinusMidpointP027RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP027Factor2559 * embedPair2542
        batchC05119MinusMidpointP027Center2559)
    (embedPair2542 batchC05119MinusMidpointP027Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP027DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP027Factor2559,
      batchC05119MinusMidpointP027Error2559, rounding2542,
      batchC05119MinusMidpointP027Radius2559]

theorem batchC05119MinusMidpointP027DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP027Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP027RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP027Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP027Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP027Rounded2559]

def batchC05119MinusMidpointP028Rounded2559 : RatPair2542 :=
  ((((-706482610747070999627) : ℚ) /
        1267650600228229401496703205376),
    (((-6454380923240777497) : ℚ) /
        316912650057057350374175801344))

noncomputable def batchC05119MinusMidpointP028Radius2559 : ℝ := ((16856759481739339 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05119MinusMidpointP028RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP028Factor2559
        batchC05119MinusMidpointP028Center2559) =
        batchC05119MinusMidpointP028Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP028RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP028Rounded2559‖ ≤
          batchC05119MinusMidpointP028Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP028Factor2559
      batchC05119MinusMidpointP028Center2559)
  rw [batchC05119MinusMidpointP028RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP028Factor2559 * embedPair2542
        batchC05119MinusMidpointP028Center2559)
    (embedPair2542 batchC05119MinusMidpointP028Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP028DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP028Factor2559,
      batchC05119MinusMidpointP028Error2559, rounding2542,
      batchC05119MinusMidpointP028Radius2559]

theorem batchC05119MinusMidpointP028DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP028Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP028RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP028Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP028Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP028Rounded2559]

def batchC05119MinusMidpointP029Rounded2559 : RatPair2542 :=
  ((((-373558811510719673843) : ℚ) /
        633825300114114700748351602688),
    (((-14308682694862249729) : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05119MinusMidpointP029Radius2559 : ℝ := ((35689448160527877 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05119MinusMidpointP029RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05119MinusMidpointP029Factor2559
        batchC05119MinusMidpointP029Center2559) =
        batchC05119MinusMidpointP029Rounded2559 := by
  cbv

theorem batchC05119MinusMidpointP029RoundedError2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05119MinusMidpointPosition2559 -
      embedPair2542 batchC05119MinusMidpointP029Rounded2559‖ ≤
          batchC05119MinusMidpointP029Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05119MinusMidpointP029Factor2559
      batchC05119MinusMidpointP029Center2559)
  rw [batchC05119MinusMidpointP029RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP029Factor2559 * embedPair2542
        batchC05119MinusMidpointP029Center2559)
    (embedPair2542 batchC05119MinusMidpointP029Rounded2559)).trans (add_le_add
        batchC05119MinusMidpointP029DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05119MinusMidpointP029Factor2559,
      batchC05119MinusMidpointP029Error2559, rounding2542,
      batchC05119MinusMidpointP029Radius2559]

theorem batchC05119MinusMidpointP029DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05119MinusMidpointPosition2559‖ ≤ 1 :=
        by
  have h := batchC05119MinusMidpoint_triangle2559
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05119MinusMidpointPosition2559)
    (embedPair2542 batchC05119MinusMidpointP029Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05119MinusMidpointP029RoundedError2559
      (embedPair_magnitude2542
      batchC05119MinusMidpointP029Rounded2559))
  apply h'.trans
  norm_num [batchC05119MinusMidpointP029Radius2559, pairMagnitude2542,
      batchC05119MinusMidpointP029Rounded2559]

noncomputable def batchC05119MinusSignedMidpointValue2559 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchC05119MinusMidpointP000Rounded2559
  | 1 => embedPair2542 batchC05119MinusMidpointP001Rounded2559
  | 2 => embedPair2542 batchC05119MinusMidpointP002Rounded2559
  | 3 => embedPair2542 batchC05119MinusMidpointP003Rounded2559
  | 4 => embedPair2542 batchC05119MinusMidpointP004Rounded2559
  | 5 => embedPair2542 batchC05119MinusMidpointP005Rounded2559
  | 6 => embedPair2542 batchC05119MinusMidpointP006Rounded2559
  | 7 => embedPair2542 batchC05119MinusMidpointP007Rounded2559
  | 8 => embedPair2542 batchC05119MinusMidpointP008Rounded2559
  | 9 => embedPair2542 batchC05119MinusMidpointP009Rounded2559
  | 10 => embedPair2542 batchC05119MinusMidpointP010Rounded2559
  | 11 => embedPair2542 batchC05119MinusMidpointP011Rounded2559
  | 12 => embedPair2542 batchC05119MinusMidpointP012Rounded2559
  | 13 => embedPair2542 batchC05119MinusMidpointP013Rounded2559
  | 14 => embedPair2542 batchC05119MinusMidpointP014Rounded2559
  | 15 => embedPair2542 batchC05119MinusMidpointP015Rounded2559
  | 16 => embedPair2542 batchC05119MinusMidpointP016Rounded2559
  | 17 => embedPair2542 batchC05119MinusMidpointP017Rounded2559
  | 18 => embedPair2542 batchC05119MinusMidpointP018Rounded2559
  | 19 => embedPair2542 batchC05119MinusMidpointP019Rounded2559
  | 20 => embedPair2542 batchC05119MinusMidpointP020Rounded2559
  | 21 => embedPair2542 batchC05119MinusMidpointP021Rounded2559
  | 22 => embedPair2542 batchC05119MinusMidpointP022Rounded2559
  | 23 => embedPair2542 batchC05119MinusMidpointP023Rounded2559
  | 24 => embedPair2542 batchC05119MinusMidpointP024Rounded2559
  | 25 => embedPair2542 batchC05119MinusMidpointP025Rounded2559
  | 26 => embedPair2542 batchC05119MinusMidpointP026Rounded2559
  | 27 => embedPair2542 batchC05119MinusMidpointP027Rounded2559
  | 28 => embedPair2542 batchC05119MinusMidpointP028Rounded2559
  | 29 => embedPair2542 batchC05119MinusMidpointP029Rounded2559
  | _ => 0

noncomputable def batchC05119MinusSignedMidpointError2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05119MinusMidpointP000Radius2559
  | 1 => batchC05119MinusMidpointP001Radius2559
  | 2 => batchC05119MinusMidpointP002Radius2559
  | 3 => batchC05119MinusMidpointP003Radius2559
  | 4 => batchC05119MinusMidpointP004Radius2559
  | 5 => batchC05119MinusMidpointP005Radius2559
  | 6 => batchC05119MinusMidpointP006Radius2559
  | 7 => batchC05119MinusMidpointP007Radius2559
  | 8 => batchC05119MinusMidpointP008Radius2559
  | 9 => batchC05119MinusMidpointP009Radius2559
  | 10 => batchC05119MinusMidpointP010Radius2559
  | 11 => batchC05119MinusMidpointP011Radius2559
  | 12 => batchC05119MinusMidpointP012Radius2559
  | 13 => batchC05119MinusMidpointP013Radius2559
  | 14 => batchC05119MinusMidpointP014Radius2559
  | 15 => batchC05119MinusMidpointP015Radius2559
  | 16 => batchC05119MinusMidpointP016Radius2559
  | 17 => batchC05119MinusMidpointP017Radius2559
  | 18 => batchC05119MinusMidpointP018Radius2559
  | 19 => batchC05119MinusMidpointP019Radius2559
  | 20 => batchC05119MinusMidpointP020Radius2559
  | 21 => batchC05119MinusMidpointP021Radius2559
  | 22 => batchC05119MinusMidpointP022Radius2559
  | 23 => batchC05119MinusMidpointP023Radius2559
  | 24 => batchC05119MinusMidpointP024Radius2559
  | 25 => batchC05119MinusMidpointP025Radius2559
  | 26 => batchC05119MinusMidpointP026Radius2559
  | 27 => batchC05119MinusMidpointP027Radius2559
  | 28 => batchC05119MinusMidpointP028Radius2559
  | 29 => batchC05119MinusMidpointP029Radius2559
  | _ => 0

theorem batchC05119MinusSignedMidpointExpError2559 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC05119MinusMidpointPosition2559 -
        batchC05119MinusSignedMidpointValue2559 i‖ ≤ batchC05119MinusSignedMidpointError2559 i :=
            by
  fin_cases i
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP000RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP001RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP002RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP003RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP004RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP005RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP006RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP007RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP008RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP009RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP010RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP011RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP012RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP013RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP014RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP015RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP016RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP017RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP018RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP019RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP020RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP021RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP022RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP023RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP024RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP025RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP026RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP027RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP028RoundedError2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP029RoundedError2559

theorem batchC05119MinusSignedMidpointUnitNorm2559 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC05119MinusMidpointPosition2559‖ ≤ 1
        := by
  fin_cases i
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP000DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP001DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP002DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP003DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP004DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP005DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP006DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP007DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP008DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP009DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP010DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP011DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP012DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP013DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP014DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP015DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP016DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP017DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP018DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP019DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP020DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP021DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP022DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP023DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP024DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP025DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP026DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP027DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP028DerivativeNorm2559
  · simpa only [batchC05119MinusSignedMidpointValue2559, batchC05119MinusSignedMidpointError2559]
      using
      batchC05119MinusMidpointP029DerivativeNorm2559

noncomputable def batchC05119MinusSignedMidpointSum2559 : ℂ := ⟨(((-(((339710067980 * 10^40
        + 1762945476307209428838835994280200183966) * 10^40
        + 4751170067318811341472979562520629045080) * 10^40
        + 3405502773951539855293575752223297618347)) : ℝ) /
        (((10830740 * 10^40
        + 9926594330452281804068089207165485823256) * 10^40
        + 8678349675968586177586448361572508999990) * 10^40
        + 23844295226942934417817982702456930304)),
    (((-(((17896768013 * 10^40
        + 8123444790078945420472838279090395141010) * 10^40
        + 7795292136441352745073504879742264321497) * 10^40
        + 3267926533480091022230642153926914492943)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216))⟩

noncomputable def batchC05119MinusSignedMidpointUpper2559 : ℝ := ((3136807822049 : ℝ) /
        100000000)

theorem batchC05119MinusSignedMidpointSum_eq2559 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchC05119MinusSignedMidpointValue2559 i) =
      batchC05119MinusSignedMidpointSum2559 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
        batchC05119MinusSignedMidpointValue2559,
      batchC05119MinusSignedMidpointSum2559, embedPair2542,
          batchC05119MinusMidpointP000Rounded2559,
      batchC05119MinusMidpointP001Rounded2559,
      batchC05119MinusMidpointP002Rounded2559,
      batchC05119MinusMidpointP003Rounded2559,
      batchC05119MinusMidpointP004Rounded2559,
      batchC05119MinusMidpointP005Rounded2559,
      batchC05119MinusMidpointP006Rounded2559,
      batchC05119MinusMidpointP007Rounded2559,
      batchC05119MinusMidpointP008Rounded2559,
      batchC05119MinusMidpointP009Rounded2559,
      batchC05119MinusMidpointP010Rounded2559,
      batchC05119MinusMidpointP011Rounded2559,
      batchC05119MinusMidpointP012Rounded2559,
      batchC05119MinusMidpointP013Rounded2559,
      batchC05119MinusMidpointP014Rounded2559,
      batchC05119MinusMidpointP015Rounded2559,
      batchC05119MinusMidpointP016Rounded2559,
      batchC05119MinusMidpointP017Rounded2559,
      batchC05119MinusMidpointP018Rounded2559,
      batchC05119MinusMidpointP019Rounded2559,
      batchC05119MinusMidpointP020Rounded2559,
      batchC05119MinusMidpointP021Rounded2559,
      batchC05119MinusMidpointP022Rounded2559,
      batchC05119MinusMidpointP023Rounded2559,
      batchC05119MinusMidpointP024Rounded2559,
      batchC05119MinusMidpointP025Rounded2559,
      batchC05119MinusMidpointP026Rounded2559,
      batchC05119MinusMidpointP027Rounded2559,
      batchC05119MinusMidpointP028Rounded2559,
      batchC05119MinusMidpointP029Rounded2559, Complex.mul_re, Complex.mul_im]

theorem batchC05119MinusSignedMidpointSum_norm2559 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC05119MinusSignedMidpointValue2559 i‖ ≤
        ((3136807822039 : ℝ)
        /
        100000000) := by
  rw [batchC05119MinusSignedMidpointSum_eq2559]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchC05119MinusSignedMidpointSum2559]

theorem batchC05119MinusSignedMidpointCharge2559 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchC05119MinusSignedMidpointError2559 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
      batchC05119MinusSignedMidpointError2559,
      batchC05119MinusMidpointP000Radius2559,
      batchC05119MinusMidpointP001Radius2559,
      batchC05119MinusMidpointP002Radius2559,
      batchC05119MinusMidpointP003Radius2559,
      batchC05119MinusMidpointP004Radius2559,
      batchC05119MinusMidpointP005Radius2559,
      batchC05119MinusMidpointP006Radius2559,
      batchC05119MinusMidpointP007Radius2559,
      batchC05119MinusMidpointP008Radius2559,
      batchC05119MinusMidpointP009Radius2559,
      batchC05119MinusMidpointP010Radius2559,
      batchC05119MinusMidpointP011Radius2559,
      batchC05119MinusMidpointP012Radius2559,
      batchC05119MinusMidpointP013Radius2559,
      batchC05119MinusMidpointP014Radius2559,
      batchC05119MinusMidpointP015Radius2559,
      batchC05119MinusMidpointP016Radius2559,
      batchC05119MinusMidpointP017Radius2559,
      batchC05119MinusMidpointP018Radius2559,
      batchC05119MinusMidpointP019Radius2559,
      batchC05119MinusMidpointP020Radius2559,
      batchC05119MinusMidpointP021Radius2559,
      batchC05119MinusMidpointP022Radius2559,
      batchC05119MinusMidpointP023Radius2559,
      batchC05119MinusMidpointP024Radius2559,
      batchC05119MinusMidpointP025Radius2559,
      batchC05119MinusMidpointP026Radius2559,
      batchC05119MinusMidpointP027Radius2559,
      batchC05119MinusMidpointP028Radius2559,
      batchC05119MinusMidpointP029Radius2559]

theorem batchC05119MinusSignedMidpointUpper_le2559 :
    signedJetUpper2539 2 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchC05119MinusMidpointPosition2559 ≤
          batchC05119MinusSignedMidpointUpper2559 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC05119MinusMidpointPosition2559‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC05119MinusSignedMidpointValue2559 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchC05119MinusSignedMidpointError2559 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (batchC05119MinusSignedMidpointExpError2559 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC05119MinusMidpointPosition2559‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchC05119MinusSignedMidpointUnitNorm2559 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC05119MinusMidpointPosition2559‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchC05119MinusSignedMidpointUpper2559
  linarith [batchC05119MinusSignedMidpointSum_norm2559, batchC05119MinusSignedMidpointCharge2559]

theorem batchC05119MinusPhysicalSecond2559 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        batchC05119MinusMidpointPosition2559‖ ≤
      batchC05119MinusSignedMidpointUpper2559 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchC05119MinusMidpointPosition2559
  exact h.trans batchC05119MinusSignedMidpointUpper_le2559

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05119MinusSignedMidpointExpError2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusSignedMidpointSum_eq2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusSignedMidpointCharge2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusSignedMidpointUpper_le2559
#print axioms ConnesWeilRH.Dev.batchC05119MinusPhysicalSecond2559
