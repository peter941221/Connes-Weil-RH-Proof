import ConnesWeilRH.Dev.C1RouteABatchC05120PlusMidpoint2559

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem batchC05120PlusMidpoint_triangle2559 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def batchC05120PlusMidpointP000Rounded2559 : RatPair2542 :=
  ((((-183940495763945674589) : ℚ) /
        1267650600228229401496703205376),
    ((17291233625871093 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120PlusMidpointP000Radius2559 : ℝ := ((17350391795379231 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120PlusMidpointP000RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP000Factor2559
        batchC05120PlusMidpointP000Center2559) =
        batchC05120PlusMidpointP000Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP000RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP000Rounded2559‖ ≤
          batchC05120PlusMidpointP000Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP000Factor2559
      batchC05120PlusMidpointP000Center2559)
  rw [batchC05120PlusMidpointP000RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP000Factor2559 * embedPair2542
        batchC05120PlusMidpointP000Center2559)
    (embedPair2542 batchC05120PlusMidpointP000Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP000DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP000Factor2559,
      batchC05120PlusMidpointP000Error2559, rounding2542,
      batchC05120PlusMidpointP000Radius2559]

theorem batchC05120PlusMidpointP000DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP000Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP000RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP000Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP000Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP000Rounded2559]

def batchC05120PlusMidpointP001Rounded2559 : RatPair2542 :=
  ((((-91737925408470581679) : ℚ) /
        633825300114114700748351602688),
    (((-17769595466047951) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120PlusMidpointP001Radius2559 : ℝ := ((17309709757978755 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120PlusMidpointP001RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP001Factor2559
        batchC05120PlusMidpointP001Center2559) =
        batchC05120PlusMidpointP001Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP001RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP001Rounded2559‖ ≤
          batchC05120PlusMidpointP001Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP001Factor2559
      batchC05120PlusMidpointP001Center2559)
  rw [batchC05120PlusMidpointP001RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP001Factor2559 * embedPair2542
        batchC05120PlusMidpointP001Center2559)
    (embedPair2542 batchC05120PlusMidpointP001Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP001DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP001Factor2559,
      batchC05120PlusMidpointP001Error2559, rounding2542,
      batchC05120PlusMidpointP001Radius2559]

theorem batchC05120PlusMidpointP001DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP001Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP001RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP001Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP001Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP001Rounded2559]

def batchC05120PlusMidpointP002Rounded2559 : RatPair2542 :=
  ((((-183235387823346688305) : ℚ) /
        1267650600228229401496703205376),
    ((35914243699854151 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120PlusMidpointP002Radius2559 : ℝ := ((17288655993512839 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120PlusMidpointP002RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP002Factor2559
        batchC05120PlusMidpointP002Center2559) =
        batchC05120PlusMidpointP002Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP002RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP002Rounded2559‖ ≤
          batchC05120PlusMidpointP002Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP002Factor2559
      batchC05120PlusMidpointP002Center2559)
  rw [batchC05120PlusMidpointP002RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP002Factor2559 * embedPair2542
        batchC05120PlusMidpointP002Center2559)
    (embedPair2542 batchC05120PlusMidpointP002Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP002DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP002Factor2559,
      batchC05120PlusMidpointP002Error2559, rounding2542,
      batchC05120PlusMidpointP002Radius2559]

theorem batchC05120PlusMidpointP002DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP002Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP002RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP002Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP002Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP002Rounded2559]

def batchC05120PlusMidpointP003Rounded2559 : RatPair2542 :=
  ((((-183100946266297838907) : ℚ) /
        1267650600228229401496703205376),
    ((5757351254971443 : ℚ) /
        158456325028528675187087900672))

noncomputable def batchC05120PlusMidpointP003Radius2559 : ℝ := ((2159610618419887 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC05120PlusMidpointP003RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP003Factor2559
        batchC05120PlusMidpointP003Center2559) =
        batchC05120PlusMidpointP003Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP003RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP003Rounded2559‖ ≤
          batchC05120PlusMidpointP003Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP003Factor2559
      batchC05120PlusMidpointP003Center2559)
  rw [batchC05120PlusMidpointP003RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP003Factor2559 * embedPair2542
        batchC05120PlusMidpointP003Center2559)
    (embedPair2542 batchC05120PlusMidpointP003Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP003DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP003Factor2559,
      batchC05120PlusMidpointP003Error2559, rounding2542,
      batchC05120PlusMidpointP003Radius2559]

theorem batchC05120PlusMidpointP003DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP003Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP003RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP003Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP003Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP003Rounded2559]

def batchC05120PlusMidpointP004Rounded2559 : RatPair2542 :=
  ((((-91510528552314328875) : ℚ) /
        633825300114114700748351602688),
    (((-26043504767182535) : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120PlusMidpointP004Radius2559 : ℝ := ((17269890242354937 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120PlusMidpointP004RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP004Factor2559
        batchC05120PlusMidpointP004Center2559) =
        batchC05120PlusMidpointP004Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP004RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP004Rounded2559‖ ≤
          batchC05120PlusMidpointP004Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP004Factor2559
      batchC05120PlusMidpointP004Center2559)
  rw [batchC05120PlusMidpointP004RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP004Factor2559 * embedPair2542
        batchC05120PlusMidpointP004Center2559)
    (embedPair2542 batchC05120PlusMidpointP004Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP004DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP004Factor2559,
      batchC05120PlusMidpointP004Error2559, rounding2542,
      batchC05120PlusMidpointP004Radius2559]

theorem batchC05120PlusMidpointP004DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP004Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP004RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP004Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP004Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP004Rounded2559]

def batchC05120PlusMidpointP005Rounded2559 : RatPair2542 :=
  ((((-864657634398094865) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusMidpointP005Radius2559 : ℝ := ((79884661840319 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120PlusMidpointP005RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP005Factor2559
        batchC05120PlusMidpointP005Center2559) =
        batchC05120PlusMidpointP005Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP005RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP005Rounded2559‖ ≤
          batchC05120PlusMidpointP005Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP005Factor2559
      batchC05120PlusMidpointP005Center2559)
  rw [batchC05120PlusMidpointP005RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP005Factor2559 * embedPair2542
        batchC05120PlusMidpointP005Center2559)
    (embedPair2542 batchC05120PlusMidpointP005Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP005DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP005Factor2559,
      batchC05120PlusMidpointP005Error2559, rounding2542,
      batchC05120PlusMidpointP005Radius2559]

theorem batchC05120PlusMidpointP005DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP005Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP005RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP005Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP005Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP005Rounded2559]

def batchC05120PlusMidpointP006Rounded2559 : RatPair2542 :=
  ((((-103898400115067305) : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusMidpointP006Radius2559 : ℝ := ((19769128466637 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120PlusMidpointP006RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP006Factor2559
        batchC05120PlusMidpointP006Center2559) =
        batchC05120PlusMidpointP006Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP006RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP006Rounded2559‖ ≤
          batchC05120PlusMidpointP006Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP006Factor2559
      batchC05120PlusMidpointP006Center2559)
  rw [batchC05120PlusMidpointP006RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP006Factor2559 * embedPair2542
        batchC05120PlusMidpointP006Center2559)
    (embedPair2542 batchC05120PlusMidpointP006Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP006DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP006Factor2559,
      batchC05120PlusMidpointP006Error2559, rounding2542,
      batchC05120PlusMidpointP006Radius2559]

theorem batchC05120PlusMidpointP006DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP006Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP006RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP006Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP006Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP006Rounded2559]

def batchC05120PlusMidpointP007Rounded2559 : RatPair2542 :=
  ((((-54061901476631533) : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def batchC05120PlusMidpointP007Radius2559 : ℝ := ((5406976782575 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05120PlusMidpointP007RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP007Factor2559
        batchC05120PlusMidpointP007Center2559) =
        batchC05120PlusMidpointP007Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP007RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP007Rounded2559‖ ≤
          batchC05120PlusMidpointP007Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP007Factor2559
      batchC05120PlusMidpointP007Center2559)
  rw [batchC05120PlusMidpointP007RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP007Factor2559 * embedPair2542
        batchC05120PlusMidpointP007Center2559)
    (embedPair2542 batchC05120PlusMidpointP007Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP007DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP007Factor2559,
      batchC05120PlusMidpointP007Error2559, rounding2542,
      batchC05120PlusMidpointP007Radius2559]

theorem batchC05120PlusMidpointP007DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP007Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP007RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP007Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP007Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP007Rounded2559]

def batchC05120PlusMidpointP008Rounded2559 : RatPair2542 :=
  ((((-24433951067878118749) : ℚ) /
        1267650600228229401496703205376),
    (((-90176611107329011) : ℚ) /
        79228162514264337593543950336))

noncomputable def batchC05120PlusMidpointP008Radius2559 : ℝ := ((2366266502585211 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120PlusMidpointP008RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP008Factor2559
        batchC05120PlusMidpointP008Center2559) =
        batchC05120PlusMidpointP008Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP008RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP008Rounded2559‖ ≤
          batchC05120PlusMidpointP008Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP008Factor2559
      batchC05120PlusMidpointP008Center2559)
  rw [batchC05120PlusMidpointP008RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP008Factor2559 * embedPair2542
        batchC05120PlusMidpointP008Center2559)
    (embedPair2542 batchC05120PlusMidpointP008Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP008DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP008Factor2559,
      batchC05120PlusMidpointP008Error2559, rounding2542,
      batchC05120PlusMidpointP008Radius2559]

theorem batchC05120PlusMidpointP008DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP008Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP008RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP008Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP008Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP008Rounded2559]

def batchC05120PlusMidpointP009Rounded2559 : RatPair2542 :=
  ((((-3323759233456253897) : ℚ) /
        79228162514264337593543950336),
    (((-1759194108645388165) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120PlusMidpointP009Radius2559 : ℝ := ((316576520179561 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem batchC05120PlusMidpointP009RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP009Factor2559
        batchC05120PlusMidpointP009Center2559) =
        batchC05120PlusMidpointP009Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP009RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP009Rounded2559‖ ≤
          batchC05120PlusMidpointP009Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP009Factor2559
      batchC05120PlusMidpointP009Center2559)
  rw [batchC05120PlusMidpointP009RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP009Factor2559 * embedPair2542
        batchC05120PlusMidpointP009Center2559)
    (embedPair2542 batchC05120PlusMidpointP009Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP009DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP009Factor2559,
      batchC05120PlusMidpointP009Error2559, rounding2542,
      batchC05120PlusMidpointP009Radius2559]

theorem batchC05120PlusMidpointP009DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP009Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP009RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP009Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP009Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP009Rounded2559]

def batchC05120PlusMidpointP010Rounded2559 : RatPair2542 :=
  ((((-9372140438565578331) : ℚ) /
        158456325028528675187087900672),
    (((-1744148145641760339) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120PlusMidpointP010Radius2559 : ℝ := ((7108446678226625 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120PlusMidpointP010RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP010Factor2559
        batchC05120PlusMidpointP010Center2559) =
        batchC05120PlusMidpointP010Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP010RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP010Rounded2559‖ ≤
          batchC05120PlusMidpointP010Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP010Factor2559
      batchC05120PlusMidpointP010Center2559)
  rw [batchC05120PlusMidpointP010RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP010Factor2559 * embedPair2542
        batchC05120PlusMidpointP010Center2559)
    (embedPair2542 batchC05120PlusMidpointP010Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP010DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP010Factor2559,
      batchC05120PlusMidpointP010Error2559, rounding2542,
      batchC05120PlusMidpointP010Radius2559]

theorem batchC05120PlusMidpointP010DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP010Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP010RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP010Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP010Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP010Rounded2559]

def batchC05120PlusMidpointP011Rounded2559 : RatPair2542 :=
  ((((-91607596240301853881) : ℚ) /
        1267650600228229401496703205376),
    (((-204391966137138883) : ℚ) /
        158456325028528675187087900672))

noncomputable def batchC05120PlusMidpointP011Radius2559 : ℝ := ((4333994408806955 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120PlusMidpointP011RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP011Factor2559
        batchC05120PlusMidpointP011Center2559) =
        batchC05120PlusMidpointP011Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP011RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP011Rounded2559‖ ≤
          batchC05120PlusMidpointP011Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP011Factor2559
      batchC05120PlusMidpointP011Center2559)
  rw [batchC05120PlusMidpointP011RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP011Factor2559 * embedPair2542
        batchC05120PlusMidpointP011Center2559)
    (embedPair2542 batchC05120PlusMidpointP011Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP011DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP011Factor2559,
      batchC05120PlusMidpointP011Error2559, rounding2542,
      batchC05120PlusMidpointP011Radius2559]

theorem batchC05120PlusMidpointP011DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP011Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP011RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP011Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP011Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP011Rounded2559]

def batchC05120PlusMidpointP012Rounded2559 : RatPair2542 :=
  ((((-110601743460522909147) : ℚ) /
        1267650600228229401496703205376),
    (((-1428091069479098353) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120PlusMidpointP012Radius2559 : ℝ := ((2612653544312441 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05120PlusMidpointP012RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP012Factor2559
        batchC05120PlusMidpointP012Center2559) =
        batchC05120PlusMidpointP012Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP012RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP012Rounded2559‖ ≤
          batchC05120PlusMidpointP012Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP012Factor2559
      batchC05120PlusMidpointP012Center2559)
  rw [batchC05120PlusMidpointP012RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP012Factor2559 * embedPair2542
        batchC05120PlusMidpointP012Center2559)
    (embedPair2542 batchC05120PlusMidpointP012Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP012DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP012Factor2559,
      batchC05120PlusMidpointP012Error2559, rounding2542,
      batchC05120PlusMidpointP012Radius2559]

theorem batchC05120PlusMidpointP012DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP012Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP012RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP012Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP012Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP012Rounded2559]

def batchC05120PlusMidpointP013Rounded2559 : RatPair2542 :=
  ((((-129478197626521732501) : ℚ) /
        1267650600228229401496703205376),
    (((-287011343415627065) : ℚ) /
        316912650057057350374175801344))

noncomputable def batchC05120PlusMidpointP013Radius2559 : ℝ := ((12224067570614081 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120PlusMidpointP013RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP013Factor2559
        batchC05120PlusMidpointP013Center2559) =
        batchC05120PlusMidpointP013Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP013RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP013Rounded2559‖ ≤
          batchC05120PlusMidpointP013Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP013Factor2559
      batchC05120PlusMidpointP013Center2559)
  rw [batchC05120PlusMidpointP013RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP013Factor2559 * embedPair2542
        batchC05120PlusMidpointP013Center2559)
    (embedPair2542 batchC05120PlusMidpointP013Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP013DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP013Factor2559,
      batchC05120PlusMidpointP013Error2559, rounding2542,
      batchC05120PlusMidpointP013Radius2559]

theorem batchC05120PlusMidpointP013DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP013Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP013RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP013Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP013Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP013Rounded2559]

def batchC05120PlusMidpointP014Rounded2559 : RatPair2542 :=
  ((((-168403653973331333823) : ℚ) /
        1267650600228229401496703205376),
    (((-373792563454220991) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120PlusMidpointP014Radius2559 : ℝ := ((3971942743748627 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05120PlusMidpointP014RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP014Factor2559
        batchC05120PlusMidpointP014Center2559) =
        batchC05120PlusMidpointP014Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP014RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP014Rounded2559‖ ≤
          batchC05120PlusMidpointP014Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP014Factor2559
      batchC05120PlusMidpointP014Center2559)
  rw [batchC05120PlusMidpointP014RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP014Factor2559 * embedPair2542
        batchC05120PlusMidpointP014Center2559)
    (embedPair2542 batchC05120PlusMidpointP014Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP014DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP014Factor2559,
      batchC05120PlusMidpointP014Error2559, rounding2542,
      batchC05120PlusMidpointP014Radius2559]

theorem batchC05120PlusMidpointP014DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP014Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP014RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP014Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP014Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP014Rounded2559]

def batchC05120PlusMidpointP015Rounded2559 : RatPair2542 :=
  ((((-199447558385301084203) : ℚ) /
        1267650600228229401496703205376),
    ((203063981531082659 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120PlusMidpointP015Radius2559 : ℝ := ((9408187995083501 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120PlusMidpointP015RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP015Factor2559
        batchC05120PlusMidpointP015Center2559) =
        batchC05120PlusMidpointP015Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP015RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP015Rounded2559‖ ≤
          batchC05120PlusMidpointP015Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP015Factor2559
      batchC05120PlusMidpointP015Center2559)
  rw [batchC05120PlusMidpointP015RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP015Factor2559 * embedPair2542
        batchC05120PlusMidpointP015Center2559)
    (embedPair2542 batchC05120PlusMidpointP015Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP015DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP015Factor2559,
      batchC05120PlusMidpointP015Error2559, rounding2542,
      batchC05120PlusMidpointP015Radius2559]

theorem batchC05120PlusMidpointP015DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP015Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP015RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP015Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP015Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP015Rounded2559]

def batchC05120PlusMidpointP016Rounded2559 : RatPair2542 :=
  ((((-55880155702662492677) : ℚ) /
        316912650057057350374175801344),
    ((548836861348078885 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120PlusMidpointP016Radius2559 : ℝ := ((2636440093008137 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC05120PlusMidpointP016RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP016Factor2559
        batchC05120PlusMidpointP016Center2559) =
        batchC05120PlusMidpointP016Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP016RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP016Rounded2559‖ ≤
          batchC05120PlusMidpointP016Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP016Factor2559
      batchC05120PlusMidpointP016Center2559)
  rw [batchC05120PlusMidpointP016RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP016Factor2559 * embedPair2542
        batchC05120PlusMidpointP016Center2559)
    (embedPair2542 batchC05120PlusMidpointP016Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP016DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP016Factor2559,
      batchC05120PlusMidpointP016Error2559, rounding2542,
      batchC05120PlusMidpointP016Radius2559]

theorem batchC05120PlusMidpointP016DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP016Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP016RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP016Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP016Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP016Rounded2559]

def batchC05120PlusMidpointP017Rounded2559 : RatPair2542 :=
  ((((-68551952319009991191) : ℚ) /
        316912650057057350374175801344),
    ((1386932319135001447 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120PlusMidpointP017Radius2559 : ℝ := ((25893693689489611 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120PlusMidpointP017RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP017Factor2559
        batchC05120PlusMidpointP017Center2559) =
        batchC05120PlusMidpointP017Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP017RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP017Rounded2559‖ ≤
          batchC05120PlusMidpointP017Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP017Factor2559
      batchC05120PlusMidpointP017Center2559)
  rw [batchC05120PlusMidpointP017RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP017Factor2559 * embedPair2542
        batchC05120PlusMidpointP017Center2559)
    (embedPair2542 batchC05120PlusMidpointP017Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP017DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP017Factor2559,
      batchC05120PlusMidpointP017Error2559, rounding2542,
      batchC05120PlusMidpointP017Radius2559]

theorem batchC05120PlusMidpointP017DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP017Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP017RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP017Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP017Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP017Rounded2559]

def batchC05120PlusMidpointP018Rounded2559 : RatPair2542 :=
  ((((-36840215263819480023) : ℚ) /
        158456325028528675187087900672),
    ((3529759491600262795 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120PlusMidpointP018Radius2559 : ℝ := ((13920825651505617 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120PlusMidpointP018RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP018Factor2559
        batchC05120PlusMidpointP018Center2559) =
        batchC05120PlusMidpointP018Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP018RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP018Rounded2559‖ ≤
          batchC05120PlusMidpointP018Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP018Factor2559
      batchC05120PlusMidpointP018Center2559)
  rw [batchC05120PlusMidpointP018RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP018Factor2559 * embedPair2542
        batchC05120PlusMidpointP018Center2559)
    (embedPair2542 batchC05120PlusMidpointP018Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP018DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP018Factor2559,
      batchC05120PlusMidpointP018Error2559, rounding2542,
      batchC05120PlusMidpointP018Radius2559]

theorem batchC05120PlusMidpointP018DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP018Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP018RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP018Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP018Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP018Rounded2559]

def batchC05120PlusMidpointP019Rounded2559 : RatPair2542 :=
  ((((-333674555892398885997) : ℚ) /
        1267650600228229401496703205376),
    ((2538758316654473731 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120PlusMidpointP019Radius2559 : ℝ := ((15773701178068867 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120PlusMidpointP019RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP019Factor2559
        batchC05120PlusMidpointP019Center2559) =
        batchC05120PlusMidpointP019Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP019RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP019Rounded2559‖ ≤
          batchC05120PlusMidpointP019Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP019Factor2559
      batchC05120PlusMidpointP019Center2559)
  rw [batchC05120PlusMidpointP019RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP019Factor2559 * embedPair2542
        batchC05120PlusMidpointP019Center2559)
    (embedPair2542 batchC05120PlusMidpointP019Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP019DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP019Factor2559,
      batchC05120PlusMidpointP019Error2559, rounding2542,
      batchC05120PlusMidpointP019Radius2559]

theorem batchC05120PlusMidpointP019DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP019Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP019RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP019Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP019Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP019Rounded2559]

def batchC05120PlusMidpointP020Rounded2559 : RatPair2542 :=
  ((((-378776919252039145471) : ℚ) /
        1267650600228229401496703205376),
    ((440054509506815099 : ℚ) /
        79228162514264337593543950336))

noncomputable def batchC05120PlusMidpointP020Radius2559 : ℝ := ((35849154371483411 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120PlusMidpointP020RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP020Factor2559
        batchC05120PlusMidpointP020Center2559) =
        batchC05120PlusMidpointP020Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP020RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP020Rounded2559‖ ≤
          batchC05120PlusMidpointP020Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP020Factor2559
      batchC05120PlusMidpointP020Center2559)
  rw [batchC05120PlusMidpointP020RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP020Factor2559 * embedPair2542
        batchC05120PlusMidpointP020Center2559)
    (embedPair2542 batchC05120PlusMidpointP020Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP020DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP020Factor2559,
      batchC05120PlusMidpointP020Error2559, rounding2542,
      batchC05120PlusMidpointP020Radius2559]

theorem batchC05120PlusMidpointP020DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP020Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP020RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP020Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP020Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP020Rounded2559]

def batchC05120PlusMidpointP021Rounded2559 : RatPair2542 :=
  ((((-418604373958996558163) : ℚ) /
        1267650600228229401496703205376),
    ((1114542937808087081 : ℚ) /
        158456325028528675187087900672))

noncomputable def batchC05120PlusMidpointP021Radius2559 : ℝ := ((39657297370555605 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120PlusMidpointP021RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP021Factor2559
        batchC05120PlusMidpointP021Center2559) =
        batchC05120PlusMidpointP021Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP021RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP021Rounded2559‖ ≤
          batchC05120PlusMidpointP021Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP021Factor2559
      batchC05120PlusMidpointP021Center2559)
  rw [batchC05120PlusMidpointP021RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP021Factor2559 * embedPair2542
        batchC05120PlusMidpointP021Center2559)
    (embedPair2542 batchC05120PlusMidpointP021Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP021DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP021Factor2559,
      batchC05120PlusMidpointP021Error2559, rounding2542,
      batchC05120PlusMidpointP021Radius2559]

theorem batchC05120PlusMidpointP021DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP021Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP021RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP021Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP021Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP021Rounded2559]

def batchC05120PlusMidpointP022Rounded2559 : RatPair2542 :=
  ((((-219879683682105091277) : ℚ) /
        633825300114114700748351602688),
    ((9963576371762156205 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120PlusMidpointP022Radius2559 : ℝ := ((41683586093847671 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC05120PlusMidpointP022RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP022Factor2559
        batchC05120PlusMidpointP022Center2559) =
        batchC05120PlusMidpointP022Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP022RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP022Rounded2559‖ ≤
          batchC05120PlusMidpointP022Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP022Factor2559
      batchC05120PlusMidpointP022Center2559)
  rw [batchC05120PlusMidpointP022RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP022Factor2559 * embedPair2542
        batchC05120PlusMidpointP022Center2559)
    (embedPair2542 batchC05120PlusMidpointP022Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP022DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP022Factor2559,
      batchC05120PlusMidpointP022Error2559, rounding2542,
      batchC05120PlusMidpointP022Radius2559]

theorem batchC05120PlusMidpointP022DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP022Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP022RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP022Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP022Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP022Rounded2559]

def batchC05120PlusMidpointP023Rounded2559 : RatPair2542 :=
  ((((-251834940474035551461) : ℚ) /
        633825300114114700748351602688),
    ((6665022735897901567 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120PlusMidpointP023Radius2559 : ℝ := ((93397640091953 : ℝ) /
        2722258935367507707706996859454145691648)

theorem batchC05120PlusMidpointP023RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP023Factor2559
        batchC05120PlusMidpointP023Center2559) =
        batchC05120PlusMidpointP023Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP023RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP023Rounded2559‖ ≤
          batchC05120PlusMidpointP023Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP023Factor2559
      batchC05120PlusMidpointP023Center2559)
  rw [batchC05120PlusMidpointP023RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP023Factor2559 * embedPair2542
        batchC05120PlusMidpointP023Center2559)
    (embedPair2542 batchC05120PlusMidpointP023Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP023DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP023Factor2559,
      batchC05120PlusMidpointP023Error2559, rounding2542,
      batchC05120PlusMidpointP023Radius2559]

theorem batchC05120PlusMidpointP023DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP023Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP023RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP023Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP023Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP023Rounded2559]

def batchC05120PlusMidpointP024Rounded2559 : RatPair2542 :=
  ((((-534492579481308767505) : ℚ) /
        1267650600228229401496703205376),
    ((941075214929611781 : ℚ) /
        79228162514264337593543950336))

noncomputable def batchC05120PlusMidpointP024Radius2559 : ℝ := ((25393215580568941 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120PlusMidpointP024RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP024Factor2559
        batchC05120PlusMidpointP024Center2559) =
        batchC05120PlusMidpointP024Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP024RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP024Rounded2559‖ ≤
          batchC05120PlusMidpointP024Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP024Factor2559
      batchC05120PlusMidpointP024Center2559)
  rw [batchC05120PlusMidpointP024RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP024Factor2559 * embedPair2542
        batchC05120PlusMidpointP024Center2559)
    (embedPair2542 batchC05120PlusMidpointP024Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP024DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP024Factor2559,
      batchC05120PlusMidpointP024Error2559, rounding2542,
      batchC05120PlusMidpointP024Radius2559]

theorem batchC05120PlusMidpointP024DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP024Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP024RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP024Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP024Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP024Rounded2559]

def batchC05120PlusMidpointP025Rounded2559 : RatPair2542 :=
  ((((-574429923105187384521) : ℚ) /
        1267650600228229401496703205376),
    ((8695088024525090639 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120PlusMidpointP025Radius2559 : ℝ := ((13659430997976753 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05120PlusMidpointP025RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP025Factor2559
        batchC05120PlusMidpointP025Center2559) =
        batchC05120PlusMidpointP025Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP025RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP025Rounded2559‖ ≤
          batchC05120PlusMidpointP025Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP025Factor2559
      batchC05120PlusMidpointP025Center2559)
  rw [batchC05120PlusMidpointP025RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP025Factor2559 * embedPair2542
        batchC05120PlusMidpointP025Center2559)
    (embedPair2542 batchC05120PlusMidpointP025Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP025DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP025Factor2559,
      batchC05120PlusMidpointP025Error2559, rounding2542,
      batchC05120PlusMidpointP025Radius2559]

theorem batchC05120PlusMidpointP025DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP025Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP025RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP025Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP025Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP025Rounded2559]

def batchC05120PlusMidpointP026Rounded2559 : RatPair2542 :=
  ((((-616728117011192675241) : ℚ) /
        1267650600228229401496703205376),
    ((9986735121476986439 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC05120PlusMidpointP026Radius2559 : ℝ := ((29362626203609309 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120PlusMidpointP026RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP026Factor2559
        batchC05120PlusMidpointP026Center2559) =
        batchC05120PlusMidpointP026Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP026RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP026Rounded2559‖ ≤
          batchC05120PlusMidpointP026Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP026Factor2559
      batchC05120PlusMidpointP026Center2559)
  rw [batchC05120PlusMidpointP026RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP026Factor2559 * embedPair2542
        batchC05120PlusMidpointP026Center2559)
    (embedPair2542 batchC05120PlusMidpointP026Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP026DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP026Factor2559,
      batchC05120PlusMidpointP026Error2559, rounding2542,
      batchC05120PlusMidpointP026Radius2559]

theorem batchC05120PlusMidpointP026DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP026Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP026RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP026Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP026Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP026Rounded2559]

def batchC05120PlusMidpointP027Rounded2559 : RatPair2542 :=
  ((((-340204214179842058811) : ℚ) /
        633825300114114700748351602688),
    ((24070621024488472567 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120PlusMidpointP027Radius2559 : ℝ := ((16223808978053165 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05120PlusMidpointP027RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP027Factor2559
        batchC05120PlusMidpointP027Center2559) =
        batchC05120PlusMidpointP027Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP027RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP027Rounded2559‖ ≤
          batchC05120PlusMidpointP027Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP027Factor2559
      batchC05120PlusMidpointP027Center2559)
  rw [batchC05120PlusMidpointP027RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP027Factor2559 * embedPair2542
        batchC05120PlusMidpointP027Center2559)
    (embedPair2542 batchC05120PlusMidpointP027Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP027DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP027Factor2559,
      batchC05120PlusMidpointP027Error2559, rounding2542,
      batchC05120PlusMidpointP027Radius2559]

theorem batchC05120PlusMidpointP027DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP027Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP027RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP027Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP027Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP027Rounded2559]

def batchC05120PlusMidpointP028Rounded2559 : RatPair2542 :=
  ((((-706482610747070999627) : ℚ) /
        1267650600228229401496703205376),
    ((25817523692963109987 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120PlusMidpointP028Radius2559 : ℝ := ((16856759481739339 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC05120PlusMidpointP028RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP028Factor2559
        batchC05120PlusMidpointP028Center2559) =
        batchC05120PlusMidpointP028Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP028RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP028Rounded2559‖ ≤
          batchC05120PlusMidpointP028Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP028Factor2559
      batchC05120PlusMidpointP028Center2559)
  rw [batchC05120PlusMidpointP028RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP028Factor2559 * embedPair2542
        batchC05120PlusMidpointP028Center2559)
    (embedPair2542 batchC05120PlusMidpointP028Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP028DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP028Factor2559,
      batchC05120PlusMidpointP028Error2559, rounding2542,
      batchC05120PlusMidpointP028Radius2559]

theorem batchC05120PlusMidpointP028DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP028Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP028RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP028Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP028Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP028Rounded2559]

def batchC05120PlusMidpointP029Rounded2559 : RatPair2542 :=
  ((((-373558811510719673843) : ℚ) /
        633825300114114700748351602688),
    ((28617365389724499457 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC05120PlusMidpointP029Radius2559 : ℝ := ((35689448160527877 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC05120PlusMidpointP029RoundCompute2559 :
    pairRound2542 (pairMul2542 batchC05120PlusMidpointP029Factor2559
        batchC05120PlusMidpointP029Center2559) =
        batchC05120PlusMidpointP029Rounded2559 := by
  cbv

theorem batchC05120PlusMidpointP029RoundedError2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05120PlusMidpointPosition2559 -
      embedPair2542 batchC05120PlusMidpointP029Rounded2559‖ ≤
          batchC05120PlusMidpointP029Radius2559 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC05120PlusMidpointP029Factor2559
      batchC05120PlusMidpointP029Center2559)
  rw [batchC05120PlusMidpointP029RoundCompute2559, embedPair_mul2542] at hr
  have h := (batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP029Factor2559 * embedPair2542
        batchC05120PlusMidpointP029Center2559)
    (embedPair2542 batchC05120PlusMidpointP029Rounded2559)).trans (add_le_add
        batchC05120PlusMidpointP029DerivativeError2559 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC05120PlusMidpointP029Factor2559,
      batchC05120PlusMidpointP029Error2559, rounding2542,
      batchC05120PlusMidpointP029Radius2559]

theorem batchC05120PlusMidpointP029DerivativeNorm2559 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05120PlusMidpointPosition2559‖ ≤ 1 := by
  have h := batchC05120PlusMidpoint_triangle2559
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC05120PlusMidpointPosition2559)
    (embedPair2542 batchC05120PlusMidpointP029Rounded2559) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC05120PlusMidpointP029RoundedError2559
      (embedPair_magnitude2542
      batchC05120PlusMidpointP029Rounded2559))
  apply h'.trans
  norm_num [batchC05120PlusMidpointP029Radius2559, pairMagnitude2542,
      batchC05120PlusMidpointP029Rounded2559]

noncomputable def batchC05120PlusSignedMidpointValue2559 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchC05120PlusMidpointP000Rounded2559
  | 1 => embedPair2542 batchC05120PlusMidpointP001Rounded2559
  | 2 => embedPair2542 batchC05120PlusMidpointP002Rounded2559
  | 3 => embedPair2542 batchC05120PlusMidpointP003Rounded2559
  | 4 => embedPair2542 batchC05120PlusMidpointP004Rounded2559
  | 5 => embedPair2542 batchC05120PlusMidpointP005Rounded2559
  | 6 => embedPair2542 batchC05120PlusMidpointP006Rounded2559
  | 7 => embedPair2542 batchC05120PlusMidpointP007Rounded2559
  | 8 => embedPair2542 batchC05120PlusMidpointP008Rounded2559
  | 9 => embedPair2542 batchC05120PlusMidpointP009Rounded2559
  | 10 => embedPair2542 batchC05120PlusMidpointP010Rounded2559
  | 11 => embedPair2542 batchC05120PlusMidpointP011Rounded2559
  | 12 => embedPair2542 batchC05120PlusMidpointP012Rounded2559
  | 13 => embedPair2542 batchC05120PlusMidpointP013Rounded2559
  | 14 => embedPair2542 batchC05120PlusMidpointP014Rounded2559
  | 15 => embedPair2542 batchC05120PlusMidpointP015Rounded2559
  | 16 => embedPair2542 batchC05120PlusMidpointP016Rounded2559
  | 17 => embedPair2542 batchC05120PlusMidpointP017Rounded2559
  | 18 => embedPair2542 batchC05120PlusMidpointP018Rounded2559
  | 19 => embedPair2542 batchC05120PlusMidpointP019Rounded2559
  | 20 => embedPair2542 batchC05120PlusMidpointP020Rounded2559
  | 21 => embedPair2542 batchC05120PlusMidpointP021Rounded2559
  | 22 => embedPair2542 batchC05120PlusMidpointP022Rounded2559
  | 23 => embedPair2542 batchC05120PlusMidpointP023Rounded2559
  | 24 => embedPair2542 batchC05120PlusMidpointP024Rounded2559
  | 25 => embedPair2542 batchC05120PlusMidpointP025Rounded2559
  | 26 => embedPair2542 batchC05120PlusMidpointP026Rounded2559
  | 27 => embedPair2542 batchC05120PlusMidpointP027Rounded2559
  | 28 => embedPair2542 batchC05120PlusMidpointP028Rounded2559
  | 29 => embedPair2542 batchC05120PlusMidpointP029Rounded2559
  | _ => 0

noncomputable def batchC05120PlusSignedMidpointError2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC05120PlusMidpointP000Radius2559
  | 1 => batchC05120PlusMidpointP001Radius2559
  | 2 => batchC05120PlusMidpointP002Radius2559
  | 3 => batchC05120PlusMidpointP003Radius2559
  | 4 => batchC05120PlusMidpointP004Radius2559
  | 5 => batchC05120PlusMidpointP005Radius2559
  | 6 => batchC05120PlusMidpointP006Radius2559
  | 7 => batchC05120PlusMidpointP007Radius2559
  | 8 => batchC05120PlusMidpointP008Radius2559
  | 9 => batchC05120PlusMidpointP009Radius2559
  | 10 => batchC05120PlusMidpointP010Radius2559
  | 11 => batchC05120PlusMidpointP011Radius2559
  | 12 => batchC05120PlusMidpointP012Radius2559
  | 13 => batchC05120PlusMidpointP013Radius2559
  | 14 => batchC05120PlusMidpointP014Radius2559
  | 15 => batchC05120PlusMidpointP015Radius2559
  | 16 => batchC05120PlusMidpointP016Radius2559
  | 17 => batchC05120PlusMidpointP017Radius2559
  | 18 => batchC05120PlusMidpointP018Radius2559
  | 19 => batchC05120PlusMidpointP019Radius2559
  | 20 => batchC05120PlusMidpointP020Radius2559
  | 21 => batchC05120PlusMidpointP021Radius2559
  | 22 => batchC05120PlusMidpointP022Radius2559
  | 23 => batchC05120PlusMidpointP023Radius2559
  | 24 => batchC05120PlusMidpointP024Radius2559
  | 25 => batchC05120PlusMidpointP025Radius2559
  | 26 => batchC05120PlusMidpointP026Radius2559
  | 27 => batchC05120PlusMidpointP027Radius2559
  | 28 => batchC05120PlusMidpointP028Radius2559
  | 29 => batchC05120PlusMidpointP029Radius2559
  | _ => 0

theorem batchC05120PlusSignedMidpointExpError2559 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC05120PlusMidpointPosition2559 -
        batchC05120PlusSignedMidpointValue2559 i‖ ≤ batchC05120PlusSignedMidpointError2559 i := by
  fin_cases i
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP000RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP001RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP002RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP003RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP004RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP005RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP006RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP007RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP008RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP009RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP010RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP011RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP012RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP013RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP014RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP015RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP016RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP017RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP018RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP019RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP020RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP021RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP022RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP023RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP024RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP025RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP026RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP027RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP028RoundedError2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP029RoundedError2559

theorem batchC05120PlusSignedMidpointUnitNorm2559 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC05120PlusMidpointPosition2559‖ ≤ 1 :=
        by
  fin_cases i
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP000DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP001DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP002DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP003DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP004DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP005DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP006DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP007DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP008DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP009DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP010DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP011DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP012DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP013DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP014DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP015DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP016DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP017DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP018DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP019DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP020DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP021DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP022DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP023DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP024DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP025DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP026DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP027DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP028DerivativeNorm2559
  · simpa only [batchC05120PlusSignedMidpointValue2559, batchC05120PlusSignedMidpointError2559]
      using
      batchC05120PlusMidpointP029DerivativeNorm2559

noncomputable def batchC05120PlusSignedMidpointSum2559 : ℂ := ⟨(((-(((1357899070513 * 10^40
        + 282454760666773821959087059918968969651) * 10^40
        + 4670018120410512769931058093954051530450) * 10^40
        + 4418572992316417313247116684499462173613)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216)),
    (((((39099982841 * 10^40
        + 9326126977427902571704861988111998031635) * 10^40
        + 3086619733986100858169093703157186346351) * 10^40
        + 9066243810673712635503142139780450203121) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216))⟩

noncomputable def batchC05120PlusSignedMidpointUpper2559 : ℝ := ((3135662385487 : ℝ) /
        100000000)

theorem batchC05120PlusSignedMidpointSum_eq2559 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchC05120PlusSignedMidpointValue2559 i) =
      batchC05120PlusSignedMidpointSum2559 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
        batchC05120PlusSignedMidpointValue2559,
      batchC05120PlusSignedMidpointSum2559, embedPair2542, batchC05120PlusMidpointP000Rounded2559,
      batchC05120PlusMidpointP001Rounded2559,
      batchC05120PlusMidpointP002Rounded2559,
      batchC05120PlusMidpointP003Rounded2559,
      batchC05120PlusMidpointP004Rounded2559,
      batchC05120PlusMidpointP005Rounded2559,
      batchC05120PlusMidpointP006Rounded2559,
      batchC05120PlusMidpointP007Rounded2559,
      batchC05120PlusMidpointP008Rounded2559,
      batchC05120PlusMidpointP009Rounded2559,
      batchC05120PlusMidpointP010Rounded2559,
      batchC05120PlusMidpointP011Rounded2559,
      batchC05120PlusMidpointP012Rounded2559,
      batchC05120PlusMidpointP013Rounded2559,
      batchC05120PlusMidpointP014Rounded2559,
      batchC05120PlusMidpointP015Rounded2559,
      batchC05120PlusMidpointP016Rounded2559,
      batchC05120PlusMidpointP017Rounded2559,
      batchC05120PlusMidpointP018Rounded2559,
      batchC05120PlusMidpointP019Rounded2559,
      batchC05120PlusMidpointP020Rounded2559,
      batchC05120PlusMidpointP021Rounded2559,
      batchC05120PlusMidpointP022Rounded2559,
      batchC05120PlusMidpointP023Rounded2559,
      batchC05120PlusMidpointP024Rounded2559,
      batchC05120PlusMidpointP025Rounded2559,
      batchC05120PlusMidpointP026Rounded2559,
      batchC05120PlusMidpointP027Rounded2559,
      batchC05120PlusMidpointP028Rounded2559,
      batchC05120PlusMidpointP029Rounded2559, Complex.mul_re, Complex.mul_im]

theorem batchC05120PlusSignedMidpointSum_norm2559 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC05120PlusSignedMidpointValue2559 i‖ ≤
        ((3135662385477 : ℝ)
        /
        100000000) := by
  rw [batchC05120PlusSignedMidpointSum_eq2559]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchC05120PlusSignedMidpointSum2559]

theorem batchC05120PlusSignedMidpointCharge2559 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchC05120PlusSignedMidpointError2559 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
      batchC05120PlusSignedMidpointError2559,
      batchC05120PlusMidpointP000Radius2559,
      batchC05120PlusMidpointP001Radius2559,
      batchC05120PlusMidpointP002Radius2559,
      batchC05120PlusMidpointP003Radius2559,
      batchC05120PlusMidpointP004Radius2559,
      batchC05120PlusMidpointP005Radius2559,
      batchC05120PlusMidpointP006Radius2559,
      batchC05120PlusMidpointP007Radius2559,
      batchC05120PlusMidpointP008Radius2559,
      batchC05120PlusMidpointP009Radius2559,
      batchC05120PlusMidpointP010Radius2559,
      batchC05120PlusMidpointP011Radius2559,
      batchC05120PlusMidpointP012Radius2559,
      batchC05120PlusMidpointP013Radius2559,
      batchC05120PlusMidpointP014Radius2559,
      batchC05120PlusMidpointP015Radius2559,
      batchC05120PlusMidpointP016Radius2559,
      batchC05120PlusMidpointP017Radius2559,
      batchC05120PlusMidpointP018Radius2559,
      batchC05120PlusMidpointP019Radius2559,
      batchC05120PlusMidpointP020Radius2559,
      batchC05120PlusMidpointP021Radius2559,
      batchC05120PlusMidpointP022Radius2559,
      batchC05120PlusMidpointP023Radius2559,
      batchC05120PlusMidpointP024Radius2559,
      batchC05120PlusMidpointP025Radius2559,
      batchC05120PlusMidpointP026Radius2559,
      batchC05120PlusMidpointP027Radius2559,
      batchC05120PlusMidpointP028Radius2559,
      batchC05120PlusMidpointP029Radius2559]

theorem batchC05120PlusSignedMidpointUpper_le2559 :
    signedJetUpper2539 2 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchC05120PlusMidpointPosition2559 ≤
          batchC05120PlusSignedMidpointUpper2559 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC05120PlusMidpointPosition2559‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC05120PlusSignedMidpointValue2559 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchC05120PlusSignedMidpointError2559 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (batchC05120PlusSignedMidpointExpError2559 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC05120PlusMidpointPosition2559‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchC05120PlusSignedMidpointUnitNorm2559 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC05120PlusMidpointPosition2559‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchC05120PlusSignedMidpointUpper2559
  linarith [batchC05120PlusSignedMidpointSum_norm2559, batchC05120PlusSignedMidpointCharge2559]

theorem batchC05120PlusPhysicalSecond2559 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        batchC05120PlusMidpointPosition2559‖ ≤
      batchC05120PlusSignedMidpointUpper2559 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchC05120PlusMidpointPosition2559
  exact h.trans batchC05120PlusSignedMidpointUpper_le2559

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC05120PlusSignedMidpointExpError2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusSignedMidpointSum_eq2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusSignedMidpointCharge2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusSignedMidpointUpper_le2559
#print axioms ConnesWeilRH.Dev.batchC05120PlusPhysicalSecond2559
