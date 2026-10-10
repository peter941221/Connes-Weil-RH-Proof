import ConnesWeilRH.Dev.C1RouteABatchC02703MinusMidpoint2654

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem batchC02703MinusMidpoint_triangle2654 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def batchC02703MinusMidpointP000Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP000Radius2654 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02703MinusMidpointP000RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP000Factor2654
        batchC02703MinusMidpointP000Center2654) =
        batchC02703MinusMidpointP000Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP000RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP000Rounded2654‖ ≤
          batchC02703MinusMidpointP000Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP000Factor2654
      batchC02703MinusMidpointP000Center2654)
  rw [batchC02703MinusMidpointP000RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP000Factor2654 * embedPair2542
        batchC02703MinusMidpointP000Center2654)
    (embedPair2542 batchC02703MinusMidpointP000Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP000DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP000Factor2654,
      batchC02703MinusMidpointP000Error2654, rounding2542,
      batchC02703MinusMidpointP000Radius2654]

theorem batchC02703MinusMidpointP000DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP000Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP000RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP000Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP000Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP000Rounded2654]

def batchC02703MinusMidpointP001Rounded2654 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP001Radius2654 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP001RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP001Factor2654
        batchC02703MinusMidpointP001Center2654) =
        batchC02703MinusMidpointP001Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP001RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP001Rounded2654‖ ≤
          batchC02703MinusMidpointP001Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP001Factor2654
      batchC02703MinusMidpointP001Center2654)
  rw [batchC02703MinusMidpointP001RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP001Factor2654 * embedPair2542
        batchC02703MinusMidpointP001Center2654)
    (embedPair2542 batchC02703MinusMidpointP001Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP001DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP001Factor2654,
      batchC02703MinusMidpointP001Error2654, rounding2542,
      batchC02703MinusMidpointP001Radius2654]

theorem batchC02703MinusMidpointP001DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP001Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP001RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP001Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP001Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP001Rounded2654]

def batchC02703MinusMidpointP002Rounded2654 : RatPair2542 :=
  (((18926439 : ℚ) /
        633825300114114700748351602688),
    (((-9923205) : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC02703MinusMidpointP002Radius2654 : ℝ := ((1099511709309 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02703MinusMidpointP002RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP002Factor2654
        batchC02703MinusMidpointP002Center2654) =
        batchC02703MinusMidpointP002Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP002RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP002Rounded2654‖ ≤
          batchC02703MinusMidpointP002Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP002Factor2654
      batchC02703MinusMidpointP002Center2654)
  rw [batchC02703MinusMidpointP002RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP002Factor2654 * embedPair2542
        batchC02703MinusMidpointP002Center2654)
    (embedPair2542 batchC02703MinusMidpointP002Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP002DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP002Factor2654,
      batchC02703MinusMidpointP002Error2654, rounding2542,
      batchC02703MinusMidpointP002Radius2654]

theorem batchC02703MinusMidpointP002DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP002Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP002RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP002Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP002Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP002Rounded2654]

def batchC02703MinusMidpointP003Rounded2654 : RatPair2542 :=
  (((330371447573693 : ℚ) /
        1267650600228229401496703205376),
    ((77605591129343 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC02703MinusMidpointP003Radius2654 : ℝ := ((1997162442831 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02703MinusMidpointP003RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP003Factor2654
        batchC02703MinusMidpointP003Center2654) =
        batchC02703MinusMidpointP003Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP003RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP003Rounded2654‖ ≤
          batchC02703MinusMidpointP003Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP003Factor2654
      batchC02703MinusMidpointP003Center2654)
  rw [batchC02703MinusMidpointP003RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP003Factor2654 * embedPair2542
        batchC02703MinusMidpointP003Center2654)
    (embedPair2542 batchC02703MinusMidpointP003Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP003DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP003Factor2654,
      batchC02703MinusMidpointP003Error2654, rounding2542,
      batchC02703MinusMidpointP003Radius2654]

theorem batchC02703MinusMidpointP003DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP003Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP003RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP003Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP003Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP003Rounded2654]

def batchC02703MinusMidpointP004Rounded2654 : RatPair2542 :=
  (((1823548104596697 : ℚ) /
        19807040628566084398385987584),
    (((-114264386222645863) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02703MinusMidpointP004Radius2654 : ℝ := ((712738017882511 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP004RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP004Factor2654
        batchC02703MinusMidpointP004Center2654) =
        batchC02703MinusMidpointP004Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP004RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP004Rounded2654‖ ≤
          batchC02703MinusMidpointP004Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP004Factor2654
      batchC02703MinusMidpointP004Center2654)
  rw [batchC02703MinusMidpointP004RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP004Factor2654 * embedPair2542
        batchC02703MinusMidpointP004Center2654)
    (embedPair2542 batchC02703MinusMidpointP004Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP004DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP004Factor2654,
      batchC02703MinusMidpointP004Error2654, rounding2542,
      batchC02703MinusMidpointP004Radius2654]

theorem batchC02703MinusMidpointP004DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP004Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP004RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP004Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP004Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP004Rounded2654]

def batchC02703MinusMidpointP005Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP005Radius2654 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02703MinusMidpointP005RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP005Factor2654
        batchC02703MinusMidpointP005Center2654) =
        batchC02703MinusMidpointP005Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP005RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP005Rounded2654‖ ≤
          batchC02703MinusMidpointP005Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP005Factor2654
      batchC02703MinusMidpointP005Center2654)
  rw [batchC02703MinusMidpointP005RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP005Factor2654 * embedPair2542
        batchC02703MinusMidpointP005Center2654)
    (embedPair2542 batchC02703MinusMidpointP005Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP005DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP005Factor2654,
      batchC02703MinusMidpointP005Error2654, rounding2542,
      batchC02703MinusMidpointP005Radius2654]

theorem batchC02703MinusMidpointP005DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP005Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP005RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP005Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP005Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP005Rounded2654]

def batchC02703MinusMidpointP006Rounded2654 : RatPair2542 :=
  (((57 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP006Radius2654 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP006RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP006Factor2654
        batchC02703MinusMidpointP006Center2654) =
        batchC02703MinusMidpointP006Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP006RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP006Rounded2654‖ ≤
          batchC02703MinusMidpointP006Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP006Factor2654
      batchC02703MinusMidpointP006Center2654)
  rw [batchC02703MinusMidpointP006RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP006Factor2654 * embedPair2542
        batchC02703MinusMidpointP006Center2654)
    (embedPair2542 batchC02703MinusMidpointP006Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP006DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP006Factor2654,
      batchC02703MinusMidpointP006Error2654, rounding2542,
      batchC02703MinusMidpointP006Radius2654]

theorem batchC02703MinusMidpointP006DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP006Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP006RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP006Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP006Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP006Rounded2654]

def batchC02703MinusMidpointP007Rounded2654 : RatPair2542 :=
  (((9233349980871 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP007Radius2654 : ℝ := ((2204131379749 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP007RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP007Factor2654
        batchC02703MinusMidpointP007Center2654) =
        batchC02703MinusMidpointP007Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP007RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP007Rounded2654‖ ≤
          batchC02703MinusMidpointP007Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP007Factor2654
      batchC02703MinusMidpointP007Center2654)
  rw [batchC02703MinusMidpointP007RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP007Factor2654 * embedPair2542
        batchC02703MinusMidpointP007Center2654)
    (embedPair2542 batchC02703MinusMidpointP007Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP007DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP007Factor2654,
      batchC02703MinusMidpointP007Error2654, rounding2542,
      batchC02703MinusMidpointP007Radius2654]

theorem batchC02703MinusMidpointP007DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP007Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP007RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP007Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP007Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP007Rounded2654]

def batchC02703MinusMidpointP008Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP008Radius2654 : ℝ := ((2199033476483 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP008RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP008Factor2654
        batchC02703MinusMidpointP008Center2654) =
        batchC02703MinusMidpointP008Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP008RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP008Rounded2654‖ ≤
          batchC02703MinusMidpointP008Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP008Factor2654
      batchC02703MinusMidpointP008Center2654)
  rw [batchC02703MinusMidpointP008RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP008Factor2654 * embedPair2542
        batchC02703MinusMidpointP008Center2654)
    (embedPair2542 batchC02703MinusMidpointP008Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP008DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP008Factor2654,
      batchC02703MinusMidpointP008Error2654, rounding2542,
      batchC02703MinusMidpointP008Radius2654]

theorem batchC02703MinusMidpointP008DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP008Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP008RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP008Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP008Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP008Rounded2654]

def batchC02703MinusMidpointP009Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP009Radius2654 : ℝ := ((34359898071 : ℝ) /
        (2 * 10^40
        + 1778071482940061661655974875633165533184))

theorem batchC02703MinusMidpointP009RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP009Factor2654
        batchC02703MinusMidpointP009Center2654) =
        batchC02703MinusMidpointP009Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP009RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP009Rounded2654‖ ≤
          batchC02703MinusMidpointP009Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP009Factor2654
      batchC02703MinusMidpointP009Center2654)
  rw [batchC02703MinusMidpointP009RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP009Factor2654 * embedPair2542
        batchC02703MinusMidpointP009Center2654)
    (embedPair2542 batchC02703MinusMidpointP009Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP009DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP009Factor2654,
      batchC02703MinusMidpointP009Error2654, rounding2542,
      batchC02703MinusMidpointP009Radius2654]

theorem batchC02703MinusMidpointP009DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP009Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP009RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP009Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP009Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP009Rounded2654]

def batchC02703MinusMidpointP010Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP010Radius2654 : ℝ := ((2199033476579 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP010RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP010Factor2654
        batchC02703MinusMidpointP010Center2654) =
        batchC02703MinusMidpointP010Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP010RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP010Rounded2654‖ ≤
          batchC02703MinusMidpointP010Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP010Factor2654
      batchC02703MinusMidpointP010Center2654)
  rw [batchC02703MinusMidpointP010RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP010Factor2654 * embedPair2542
        batchC02703MinusMidpointP010Center2654)
    (embedPair2542 batchC02703MinusMidpointP010Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP010DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP010Factor2654,
      batchC02703MinusMidpointP010Error2654, rounding2542,
      batchC02703MinusMidpointP010Radius2654]

theorem batchC02703MinusMidpointP010DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP010Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP010RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP010Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP010Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP010Rounded2654]

def batchC02703MinusMidpointP011Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP011Radius2654 : ℝ := ((1099516738301 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02703MinusMidpointP011RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP011Factor2654
        batchC02703MinusMidpointP011Center2654) =
        batchC02703MinusMidpointP011Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP011RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP011Rounded2654‖ ≤
          batchC02703MinusMidpointP011Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP011Factor2654
      batchC02703MinusMidpointP011Center2654)
  rw [batchC02703MinusMidpointP011RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP011Factor2654 * embedPair2542
        batchC02703MinusMidpointP011Center2654)
    (embedPair2542 batchC02703MinusMidpointP011Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP011DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP011Factor2654,
      batchC02703MinusMidpointP011Error2654, rounding2542,
      batchC02703MinusMidpointP011Radius2654]

theorem batchC02703MinusMidpointP011DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP011Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP011RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP011Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP011Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP011Rounded2654]

def batchC02703MinusMidpointP012Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP012Radius2654 : ℝ := ((2199033476627 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP012RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP012Factor2654
        batchC02703MinusMidpointP012Center2654) =
        batchC02703MinusMidpointP012Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP012RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP012Rounded2654‖ ≤
          batchC02703MinusMidpointP012Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP012Factor2654
      batchC02703MinusMidpointP012Center2654)
  rw [batchC02703MinusMidpointP012RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP012Factor2654 * embedPair2542
        batchC02703MinusMidpointP012Center2654)
    (embedPair2542 batchC02703MinusMidpointP012Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP012DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP012Factor2654,
      batchC02703MinusMidpointP012Error2654, rounding2542,
      batchC02703MinusMidpointP012Radius2654]

theorem batchC02703MinusMidpointP012DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP012Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP012RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP012Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP012Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP012Rounded2654]

def batchC02703MinusMidpointP013Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP013Radius2654 : ℝ := ((2199033476649 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP013RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP013Factor2654
        batchC02703MinusMidpointP013Center2654) =
        batchC02703MinusMidpointP013Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP013RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP013Rounded2654‖ ≤
          batchC02703MinusMidpointP013Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP013Factor2654
      batchC02703MinusMidpointP013Center2654)
  rw [batchC02703MinusMidpointP013RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP013Factor2654 * embedPair2542
        batchC02703MinusMidpointP013Center2654)
    (embedPair2542 batchC02703MinusMidpointP013Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP013DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP013Factor2654,
      batchC02703MinusMidpointP013Error2654, rounding2542,
      batchC02703MinusMidpointP013Radius2654]

theorem batchC02703MinusMidpointP013DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP013Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP013RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP013Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP013Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP013Rounded2654]

def batchC02703MinusMidpointP014Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP014Radius2654 : ℝ := ((1099516738345 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02703MinusMidpointP014RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP014Factor2654
        batchC02703MinusMidpointP014Center2654) =
        batchC02703MinusMidpointP014Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP014RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP014Rounded2654‖ ≤
          batchC02703MinusMidpointP014Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP014Factor2654
      batchC02703MinusMidpointP014Center2654)
  rw [batchC02703MinusMidpointP014RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP014Factor2654 * embedPair2542
        batchC02703MinusMidpointP014Center2654)
    (embedPair2542 batchC02703MinusMidpointP014Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP014DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP014Factor2654,
      batchC02703MinusMidpointP014Error2654, rounding2542,
      batchC02703MinusMidpointP014Radius2654]

theorem batchC02703MinusMidpointP014DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP014Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP014RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP014Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP014Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP014Rounded2654]

def batchC02703MinusMidpointP015Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP015Radius2654 : ℝ := ((2199033476719 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP015RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP015Factor2654
        batchC02703MinusMidpointP015Center2654) =
        batchC02703MinusMidpointP015Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP015RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP015Rounded2654‖ ≤
          batchC02703MinusMidpointP015Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP015Factor2654
      batchC02703MinusMidpointP015Center2654)
  rw [batchC02703MinusMidpointP015RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP015Factor2654 * embedPair2542
        batchC02703MinusMidpointP015Center2654)
    (embedPair2542 batchC02703MinusMidpointP015Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP015DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP015Factor2654,
      batchC02703MinusMidpointP015Error2654, rounding2542,
      batchC02703MinusMidpointP015Radius2654]

theorem batchC02703MinusMidpointP015DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP015Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP015RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP015Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP015Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP015Rounded2654]

def batchC02703MinusMidpointP016Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP016Radius2654 : ℝ := ((2199033476741 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP016RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP016Factor2654
        batchC02703MinusMidpointP016Center2654) =
        batchC02703MinusMidpointP016Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP016RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP016Rounded2654‖ ≤
          batchC02703MinusMidpointP016Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP016Factor2654
      batchC02703MinusMidpointP016Center2654)
  rw [batchC02703MinusMidpointP016RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP016Factor2654 * embedPair2542
        batchC02703MinusMidpointP016Center2654)
    (embedPair2542 batchC02703MinusMidpointP016Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP016DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP016Factor2654,
      batchC02703MinusMidpointP016Error2654, rounding2542,
      batchC02703MinusMidpointP016Radius2654]

theorem batchC02703MinusMidpointP016DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP016Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP016RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP016Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP016Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP016Rounded2654]

def batchC02703MinusMidpointP017Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP017Radius2654 : ℝ := ((1099516738391 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02703MinusMidpointP017RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP017Factor2654
        batchC02703MinusMidpointP017Center2654) =
        batchC02703MinusMidpointP017Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP017RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP017Rounded2654‖ ≤
          batchC02703MinusMidpointP017Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP017Factor2654
      batchC02703MinusMidpointP017Center2654)
  rw [batchC02703MinusMidpointP017RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP017Factor2654 * embedPair2542
        batchC02703MinusMidpointP017Center2654)
    (embedPair2542 batchC02703MinusMidpointP017Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP017DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP017Factor2654,
      batchC02703MinusMidpointP017Error2654, rounding2542,
      batchC02703MinusMidpointP017Radius2654]

theorem batchC02703MinusMidpointP017DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP017Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP017RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP017Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP017Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP017Rounded2654]

def batchC02703MinusMidpointP018Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP018Radius2654 : ℝ := ((2199033476797 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP018RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP018Factor2654
        batchC02703MinusMidpointP018Center2654) =
        batchC02703MinusMidpointP018Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP018RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP018Rounded2654‖ ≤
          batchC02703MinusMidpointP018Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP018Factor2654
      batchC02703MinusMidpointP018Center2654)
  rw [batchC02703MinusMidpointP018RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP018Factor2654 * embedPair2542
        batchC02703MinusMidpointP018Center2654)
    (embedPair2542 batchC02703MinusMidpointP018Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP018DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP018Factor2654,
      batchC02703MinusMidpointP018Error2654, rounding2542,
      batchC02703MinusMidpointP018Radius2654]

theorem batchC02703MinusMidpointP018DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP018Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP018RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP018Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP018Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP018Rounded2654]

def batchC02703MinusMidpointP019Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP019Radius2654 : ℝ := ((1099516738413 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02703MinusMidpointP019RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP019Factor2654
        batchC02703MinusMidpointP019Center2654) =
        batchC02703MinusMidpointP019Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP019RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP019Rounded2654‖ ≤
          batchC02703MinusMidpointP019Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP019Factor2654
      batchC02703MinusMidpointP019Center2654)
  rw [batchC02703MinusMidpointP019RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP019Factor2654 * embedPair2542
        batchC02703MinusMidpointP019Center2654)
    (embedPair2542 batchC02703MinusMidpointP019Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP019DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP019Factor2654,
      batchC02703MinusMidpointP019Error2654, rounding2542,
      batchC02703MinusMidpointP019Radius2654]

theorem batchC02703MinusMidpointP019DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP019Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP019RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP019Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP019Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP019Rounded2654]

def batchC02703MinusMidpointP020Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP020Radius2654 : ℝ := ((274879184607 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02703MinusMidpointP020RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP020Factor2654
        batchC02703MinusMidpointP020Center2654) =
        batchC02703MinusMidpointP020Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP020RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP020Rounded2654‖ ≤
          batchC02703MinusMidpointP020Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP020Factor2654
      batchC02703MinusMidpointP020Center2654)
  rw [batchC02703MinusMidpointP020RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP020Factor2654 * embedPair2542
        batchC02703MinusMidpointP020Center2654)
    (embedPair2542 batchC02703MinusMidpointP020Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP020DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP020Factor2654,
      batchC02703MinusMidpointP020Error2654, rounding2542,
      batchC02703MinusMidpointP020Radius2654]

theorem batchC02703MinusMidpointP020DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP020Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP020RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP020Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP020Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP020Rounded2654]

def batchC02703MinusMidpointP021Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP021Radius2654 : ℝ := ((1099516738441 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02703MinusMidpointP021RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP021Factor2654
        batchC02703MinusMidpointP021Center2654) =
        batchC02703MinusMidpointP021Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP021RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP021Rounded2654‖ ≤
          batchC02703MinusMidpointP021Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP021Factor2654
      batchC02703MinusMidpointP021Center2654)
  rw [batchC02703MinusMidpointP021RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP021Factor2654 * embedPair2542
        batchC02703MinusMidpointP021Center2654)
    (embedPair2542 batchC02703MinusMidpointP021Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP021DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP021Factor2654,
      batchC02703MinusMidpointP021Error2654, rounding2542,
      batchC02703MinusMidpointP021Radius2654]

theorem batchC02703MinusMidpointP021DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP021Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP021RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP021Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP021Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP021Rounded2654]

def batchC02703MinusMidpointP022Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP022Radius2654 : ℝ := ((2199033476895 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP022RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP022Factor2654
        batchC02703MinusMidpointP022Center2654) =
        batchC02703MinusMidpointP022Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP022RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP022Rounded2654‖ ≤
          batchC02703MinusMidpointP022Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP022Factor2654
      batchC02703MinusMidpointP022Center2654)
  rw [batchC02703MinusMidpointP022RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP022Factor2654 * embedPair2542
        batchC02703MinusMidpointP022Center2654)
    (embedPair2542 batchC02703MinusMidpointP022Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP022DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP022Factor2654,
      batchC02703MinusMidpointP022Error2654, rounding2542,
      batchC02703MinusMidpointP022Radius2654]

theorem batchC02703MinusMidpointP022DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP022Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP022RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP022Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP022Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP022Rounded2654]

def batchC02703MinusMidpointP023Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP023Radius2654 : ℝ := ((2199033476933 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP023RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP023Factor2654
        batchC02703MinusMidpointP023Center2654) =
        batchC02703MinusMidpointP023Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP023RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP023Rounded2654‖ ≤
          batchC02703MinusMidpointP023Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP023Factor2654
      batchC02703MinusMidpointP023Center2654)
  rw [batchC02703MinusMidpointP023RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP023Factor2654 * embedPair2542
        batchC02703MinusMidpointP023Center2654)
    (embedPair2542 batchC02703MinusMidpointP023Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP023DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP023Factor2654,
      batchC02703MinusMidpointP023Error2654, rounding2542,
      batchC02703MinusMidpointP023Radius2654]

theorem batchC02703MinusMidpointP023DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP023Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP023RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP023Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP023Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP023Rounded2654]

def batchC02703MinusMidpointP024Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP024Radius2654 : ℝ := ((1099516738475 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02703MinusMidpointP024RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP024Factor2654
        batchC02703MinusMidpointP024Center2654) =
        batchC02703MinusMidpointP024Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP024RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP024Rounded2654‖ ≤
          batchC02703MinusMidpointP024Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP024Factor2654
      batchC02703MinusMidpointP024Center2654)
  rw [batchC02703MinusMidpointP024RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP024Factor2654 * embedPair2542
        batchC02703MinusMidpointP024Center2654)
    (embedPair2542 batchC02703MinusMidpointP024Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP024DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP024Factor2654,
      batchC02703MinusMidpointP024Error2654, rounding2542,
      batchC02703MinusMidpointP024Radius2654]

theorem batchC02703MinusMidpointP024DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP024Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP024RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP024Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP024Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP024Rounded2654]

def batchC02703MinusMidpointP025Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP025Radius2654 : ℝ := ((549758369243 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02703MinusMidpointP025RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP025Factor2654
        batchC02703MinusMidpointP025Center2654) =
        batchC02703MinusMidpointP025Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP025RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP025Rounded2654‖ ≤
          batchC02703MinusMidpointP025Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP025Factor2654
      batchC02703MinusMidpointP025Center2654)
  rw [batchC02703MinusMidpointP025RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP025Factor2654 * embedPair2542
        batchC02703MinusMidpointP025Center2654)
    (embedPair2542 batchC02703MinusMidpointP025Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP025DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP025Factor2654,
      batchC02703MinusMidpointP025Error2654, rounding2542,
      batchC02703MinusMidpointP025Radius2654]

theorem batchC02703MinusMidpointP025DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP025Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP025RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP025Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP025Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP025Rounded2654]

def batchC02703MinusMidpointP026Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP026Radius2654 : ℝ := ((1099516738497 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02703MinusMidpointP026RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP026Factor2654
        batchC02703MinusMidpointP026Center2654) =
        batchC02703MinusMidpointP026Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP026RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP026Rounded2654‖ ≤
          batchC02703MinusMidpointP026Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP026Factor2654
      batchC02703MinusMidpointP026Center2654)
  rw [batchC02703MinusMidpointP026RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP026Factor2654 * embedPair2542
        batchC02703MinusMidpointP026Center2654)
    (embedPair2542 batchC02703MinusMidpointP026Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP026DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP026Factor2654,
      batchC02703MinusMidpointP026Error2654, rounding2542,
      batchC02703MinusMidpointP026Radius2654]

theorem batchC02703MinusMidpointP026DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP026Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP026RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP026Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP026Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP026Rounded2654]

def batchC02703MinusMidpointP027Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP027Radius2654 : ℝ := ((1099516738513 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02703MinusMidpointP027RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP027Factor2654
        batchC02703MinusMidpointP027Center2654) =
        batchC02703MinusMidpointP027Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP027RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP027Rounded2654‖ ≤
          batchC02703MinusMidpointP027Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP027Factor2654
      batchC02703MinusMidpointP027Center2654)
  rw [batchC02703MinusMidpointP027RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP027Factor2654 * embedPair2542
        batchC02703MinusMidpointP027Center2654)
    (embedPair2542 batchC02703MinusMidpointP027Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP027DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP027Factor2654,
      batchC02703MinusMidpointP027Error2654, rounding2542,
      batchC02703MinusMidpointP027Radius2654]

theorem batchC02703MinusMidpointP027DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP027Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP027RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP027Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP027Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP027Rounded2654]

def batchC02703MinusMidpointP028Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP028Radius2654 : ℝ := ((2199033477039 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP028RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP028Factor2654
        batchC02703MinusMidpointP028Center2654) =
        batchC02703MinusMidpointP028Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP028RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP028Rounded2654‖ ≤
          batchC02703MinusMidpointP028Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP028Factor2654
      batchC02703MinusMidpointP028Center2654)
  rw [batchC02703MinusMidpointP028RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP028Factor2654 * embedPair2542
        batchC02703MinusMidpointP028Center2654)
    (embedPair2542 batchC02703MinusMidpointP028Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP028DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP028Factor2654,
      batchC02703MinusMidpointP028Error2654, rounding2542,
      batchC02703MinusMidpointP028Radius2654]

theorem batchC02703MinusMidpointP028DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP028Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP028RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP028Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP028Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP028Rounded2654]

def batchC02703MinusMidpointP029Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP029Radius2654 : ℝ := ((2199033477059 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703MinusMidpointP029RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703MinusMidpointP029Factor2654
        batchC02703MinusMidpointP029Center2654) =
        batchC02703MinusMidpointP029Rounded2654 := by
  cbv

theorem batchC02703MinusMidpointP029RoundedError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP029Rounded2654‖ ≤
          batchC02703MinusMidpointP029Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703MinusMidpointP029Factor2654
      batchC02703MinusMidpointP029Center2654)
  rw [batchC02703MinusMidpointP029RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP029Factor2654 * embedPair2542
        batchC02703MinusMidpointP029Center2654)
    (embedPair2542 batchC02703MinusMidpointP029Rounded2654)).trans (add_le_add
        batchC02703MinusMidpointP029DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703MinusMidpointP029Factor2654,
      batchC02703MinusMidpointP029Error2654, rounding2542,
      batchC02703MinusMidpointP029Radius2654]

theorem batchC02703MinusMidpointP029DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02703MinusMidpointPosition2654‖ ≤ 1 :=
        by
  have h := batchC02703MinusMidpoint_triangle2654
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02703MinusMidpointPosition2654)
    (embedPair2542 batchC02703MinusMidpointP029Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703MinusMidpointP029RoundedError2654
      (embedPair_magnitude2542
      batchC02703MinusMidpointP029Rounded2654))
  apply h'.trans
  norm_num [batchC02703MinusMidpointP029Radius2654, pairMagnitude2542,
      batchC02703MinusMidpointP029Rounded2654]

noncomputable def batchC02703MinusSignedMidpointValue2654 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchC02703MinusMidpointP000Rounded2654
  | 1 => embedPair2542 batchC02703MinusMidpointP001Rounded2654
  | 2 => embedPair2542 batchC02703MinusMidpointP002Rounded2654
  | 3 => embedPair2542 batchC02703MinusMidpointP003Rounded2654
  | 4 => embedPair2542 batchC02703MinusMidpointP004Rounded2654
  | 5 => embedPair2542 batchC02703MinusMidpointP005Rounded2654
  | 6 => embedPair2542 batchC02703MinusMidpointP006Rounded2654
  | 7 => embedPair2542 batchC02703MinusMidpointP007Rounded2654
  | 8 => embedPair2542 batchC02703MinusMidpointP008Rounded2654
  | 9 => embedPair2542 batchC02703MinusMidpointP009Rounded2654
  | 10 => embedPair2542 batchC02703MinusMidpointP010Rounded2654
  | 11 => embedPair2542 batchC02703MinusMidpointP011Rounded2654
  | 12 => embedPair2542 batchC02703MinusMidpointP012Rounded2654
  | 13 => embedPair2542 batchC02703MinusMidpointP013Rounded2654
  | 14 => embedPair2542 batchC02703MinusMidpointP014Rounded2654
  | 15 => embedPair2542 batchC02703MinusMidpointP015Rounded2654
  | 16 => embedPair2542 batchC02703MinusMidpointP016Rounded2654
  | 17 => embedPair2542 batchC02703MinusMidpointP017Rounded2654
  | 18 => embedPair2542 batchC02703MinusMidpointP018Rounded2654
  | 19 => embedPair2542 batchC02703MinusMidpointP019Rounded2654
  | 20 => embedPair2542 batchC02703MinusMidpointP020Rounded2654
  | 21 => embedPair2542 batchC02703MinusMidpointP021Rounded2654
  | 22 => embedPair2542 batchC02703MinusMidpointP022Rounded2654
  | 23 => embedPair2542 batchC02703MinusMidpointP023Rounded2654
  | 24 => embedPair2542 batchC02703MinusMidpointP024Rounded2654
  | 25 => embedPair2542 batchC02703MinusMidpointP025Rounded2654
  | 26 => embedPair2542 batchC02703MinusMidpointP026Rounded2654
  | 27 => embedPair2542 batchC02703MinusMidpointP027Rounded2654
  | 28 => embedPair2542 batchC02703MinusMidpointP028Rounded2654
  | 29 => embedPair2542 batchC02703MinusMidpointP029Rounded2654
  | _ => 0

noncomputable def batchC02703MinusSignedMidpointError2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02703MinusMidpointP000Radius2654
  | 1 => batchC02703MinusMidpointP001Radius2654
  | 2 => batchC02703MinusMidpointP002Radius2654
  | 3 => batchC02703MinusMidpointP003Radius2654
  | 4 => batchC02703MinusMidpointP004Radius2654
  | 5 => batchC02703MinusMidpointP005Radius2654
  | 6 => batchC02703MinusMidpointP006Radius2654
  | 7 => batchC02703MinusMidpointP007Radius2654
  | 8 => batchC02703MinusMidpointP008Radius2654
  | 9 => batchC02703MinusMidpointP009Radius2654
  | 10 => batchC02703MinusMidpointP010Radius2654
  | 11 => batchC02703MinusMidpointP011Radius2654
  | 12 => batchC02703MinusMidpointP012Radius2654
  | 13 => batchC02703MinusMidpointP013Radius2654
  | 14 => batchC02703MinusMidpointP014Radius2654
  | 15 => batchC02703MinusMidpointP015Radius2654
  | 16 => batchC02703MinusMidpointP016Radius2654
  | 17 => batchC02703MinusMidpointP017Radius2654
  | 18 => batchC02703MinusMidpointP018Radius2654
  | 19 => batchC02703MinusMidpointP019Radius2654
  | 20 => batchC02703MinusMidpointP020Radius2654
  | 21 => batchC02703MinusMidpointP021Radius2654
  | 22 => batchC02703MinusMidpointP022Radius2654
  | 23 => batchC02703MinusMidpointP023Radius2654
  | 24 => batchC02703MinusMidpointP024Radius2654
  | 25 => batchC02703MinusMidpointP025Radius2654
  | 26 => batchC02703MinusMidpointP026Radius2654
  | 27 => batchC02703MinusMidpointP027Radius2654
  | 28 => batchC02703MinusMidpointP028Radius2654
  | 29 => batchC02703MinusMidpointP029Radius2654
  | _ => 0

theorem batchC02703MinusSignedMidpointExpError2654 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02703MinusMidpointPosition2654 -
        batchC02703MinusSignedMidpointValue2654 i‖ ≤ batchC02703MinusSignedMidpointError2654 i :=
            by
  fin_cases i
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP000RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP001RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP002RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP003RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP004RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP005RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP006RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP007RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP008RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP009RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP010RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP011RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP012RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP013RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP014RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP015RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP016RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP017RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP018RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP019RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP020RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP021RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP022RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP023RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP024RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP025RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP026RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP027RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP028RoundedError2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP029RoundedError2654

theorem batchC02703MinusSignedMidpointUnitNorm2654 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02703MinusMidpointPosition2654‖ ≤ 1
        := by
  fin_cases i
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP000DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP001DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP002DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP003DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP004DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP005DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP006DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP007DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP008DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP009DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP010DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP011DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP012DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP013DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP014DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP015DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP016DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP017DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP018DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP019DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP020DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP021DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP022DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP023DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP024DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP025DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP026DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP027DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP028DerivativeNorm2654
  · simpa only [batchC02703MinusSignedMidpointValue2654, batchC02703MinusSignedMidpointError2654]
      using
      batchC02703MinusMidpointP029DerivativeNorm2654

noncomputable def batchC02703MinusSignedMidpointSum2654 : ℂ := ⟨(((-(((79346 * 10^40
        + 2229333951943519596473339258075417053754) * 10^40
        + 8405288758097578340932041861314674590030) * 10^40
        + 6176848536269528708137024373317279985325)) : ℝ) /
        (((21661481 * 10^40
        + 9853188660904563608136178414330971646513) * 10^40
        + 7356699351937172355172896723145017999980) * 10^40
        + 47688590453885868835635965404913860608)),
    (((-(((9211 * 10^40
        + 8635129018035896376305082489920162115524) * 10^40
        + 3692587235174045143544556232011146739419) * 10^40
        + 5919925736269589485237641233320294910973)) : ℝ) /
        (((21661481 * 10^40
        + 9853188660904563608136178414330971646513) * 10^40
        + 7356699351937172355172896723145017999980) * 10^40
        + 47688590453885868835635965404913860608))⟩

noncomputable def batchC02703MinusSignedMidpointUpper2654 : ℝ := ((92193 : ℝ) /
        25000000)

theorem batchC02703MinusSignedMidpointSum_eq2654 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02703MinusSignedMidpointValue2654 i) =
      batchC02703MinusSignedMidpointSum2654 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
        batchC02703MinusSignedMidpointValue2654,
      batchC02703MinusSignedMidpointSum2654, embedPair2542,
          batchC02703MinusMidpointP000Rounded2654,
      batchC02703MinusMidpointP001Rounded2654,
      batchC02703MinusMidpointP002Rounded2654,
      batchC02703MinusMidpointP003Rounded2654,
      batchC02703MinusMidpointP004Rounded2654,
      batchC02703MinusMidpointP005Rounded2654,
      batchC02703MinusMidpointP006Rounded2654,
      batchC02703MinusMidpointP007Rounded2654,
      batchC02703MinusMidpointP008Rounded2654,
      batchC02703MinusMidpointP009Rounded2654,
      batchC02703MinusMidpointP010Rounded2654,
      batchC02703MinusMidpointP011Rounded2654,
      batchC02703MinusMidpointP012Rounded2654,
      batchC02703MinusMidpointP013Rounded2654,
      batchC02703MinusMidpointP014Rounded2654,
      batchC02703MinusMidpointP015Rounded2654,
      batchC02703MinusMidpointP016Rounded2654,
      batchC02703MinusMidpointP017Rounded2654,
      batchC02703MinusMidpointP018Rounded2654,
      batchC02703MinusMidpointP019Rounded2654,
      batchC02703MinusMidpointP020Rounded2654,
      batchC02703MinusMidpointP021Rounded2654,
      batchC02703MinusMidpointP022Rounded2654,
      batchC02703MinusMidpointP023Rounded2654,
      batchC02703MinusMidpointP024Rounded2654,
      batchC02703MinusMidpointP025Rounded2654,
      batchC02703MinusMidpointP026Rounded2654,
      batchC02703MinusMidpointP027Rounded2654,
      batchC02703MinusMidpointP028Rounded2654,
      batchC02703MinusMidpointP029Rounded2654, Complex.mul_re, Complex.mul_im]

theorem batchC02703MinusSignedMidpointSum_norm2654 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02703MinusSignedMidpointValue2654 i‖ ≤
        ((184381 : ℝ) /
        50000000) := by
  rw [batchC02703MinusSignedMidpointSum_eq2654]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchC02703MinusSignedMidpointSum2654]

theorem batchC02703MinusSignedMidpointCharge2654 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchC02703MinusSignedMidpointError2654 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
      batchC02703MinusSignedMidpointError2654,
      batchC02703MinusMidpointP000Radius2654,
      batchC02703MinusMidpointP001Radius2654,
      batchC02703MinusMidpointP002Radius2654,
      batchC02703MinusMidpointP003Radius2654,
      batchC02703MinusMidpointP004Radius2654,
      batchC02703MinusMidpointP005Radius2654,
      batchC02703MinusMidpointP006Radius2654,
      batchC02703MinusMidpointP007Radius2654,
      batchC02703MinusMidpointP008Radius2654,
      batchC02703MinusMidpointP009Radius2654,
      batchC02703MinusMidpointP010Radius2654,
      batchC02703MinusMidpointP011Radius2654,
      batchC02703MinusMidpointP012Radius2654,
      batchC02703MinusMidpointP013Radius2654,
      batchC02703MinusMidpointP014Radius2654,
      batchC02703MinusMidpointP015Radius2654,
      batchC02703MinusMidpointP016Radius2654,
      batchC02703MinusMidpointP017Radius2654,
      batchC02703MinusMidpointP018Radius2654,
      batchC02703MinusMidpointP019Radius2654,
      batchC02703MinusMidpointP020Radius2654,
      batchC02703MinusMidpointP021Radius2654,
      batchC02703MinusMidpointP022Radius2654,
      batchC02703MinusMidpointP023Radius2654,
      batchC02703MinusMidpointP024Radius2654,
      batchC02703MinusMidpointP025Radius2654,
      batchC02703MinusMidpointP026Radius2654,
      batchC02703MinusMidpointP027Radius2654,
      batchC02703MinusMidpointP028Radius2654,
      batchC02703MinusMidpointP029Radius2654]

theorem batchC02703MinusSignedMidpointUpper_le2654 :
    signedJetUpper2539 2 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchC02703MinusMidpointPosition2654 ≤
          batchC02703MinusSignedMidpointUpper2654 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02703MinusMidpointPosition2654‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02703MinusSignedMidpointValue2654 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchC02703MinusSignedMidpointError2654 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (batchC02703MinusSignedMidpointExpError2654 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02703MinusMidpointPosition2654‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchC02703MinusSignedMidpointUnitNorm2654 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02703MinusMidpointPosition2654‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchC02703MinusSignedMidpointUpper2654
  linarith [batchC02703MinusSignedMidpointSum_norm2654, batchC02703MinusSignedMidpointCharge2654]

theorem batchC02703MinusPhysicalSecond2654 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        batchC02703MinusMidpointPosition2654‖ ≤
      batchC02703MinusSignedMidpointUpper2654 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchC02703MinusMidpointPosition2654
  exact h.trans batchC02703MinusSignedMidpointUpper_le2654

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02703MinusSignedMidpointExpError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusSignedMidpointSum_eq2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusSignedMidpointCharge2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusSignedMidpointUpper_le2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusPhysicalSecond2654
