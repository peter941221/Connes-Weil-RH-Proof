import ConnesWeilRH.Dev.C1RouteABatchC02702MinusMidpoint2558

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem batchC02702MinusMidpoint_triangle2558 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def batchC02702MinusMidpointP000Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP000Radius2558 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02702MinusMidpointP000RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP000Factor2558
        batchC02702MinusMidpointP000Center2558) =
        batchC02702MinusMidpointP000Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP000RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP000Rounded2558‖ ≤
          batchC02702MinusMidpointP000Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP000Factor2558
      batchC02702MinusMidpointP000Center2558)
  rw [batchC02702MinusMidpointP000RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP000Factor2558 * embedPair2542
        batchC02702MinusMidpointP000Center2558)
    (embedPair2542 batchC02702MinusMidpointP000Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP000DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP000Factor2558,
      batchC02702MinusMidpointP000Error2558, rounding2542,
      batchC02702MinusMidpointP000Radius2558]

theorem batchC02702MinusMidpointP000DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP000Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP000RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP000Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP000Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP000Rounded2558]

def batchC02702MinusMidpointP001Rounded2558 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP001Radius2558 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP001RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP001Factor2558
        batchC02702MinusMidpointP001Center2558) =
        batchC02702MinusMidpointP001Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP001RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP001Rounded2558‖ ≤
          batchC02702MinusMidpointP001Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP001Factor2558
      batchC02702MinusMidpointP001Center2558)
  rw [batchC02702MinusMidpointP001RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP001Factor2558 * embedPair2542
        batchC02702MinusMidpointP001Center2558)
    (embedPair2542 batchC02702MinusMidpointP001Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP001DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP001Factor2558,
      batchC02702MinusMidpointP001Error2558, rounding2542,
      batchC02702MinusMidpointP001Radius2558]

theorem batchC02702MinusMidpointP001DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP001Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP001RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP001Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP001Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP001Rounded2558]

def batchC02702MinusMidpointP002Rounded2558 : RatPair2542 :=
  (((17479059 : ℚ) /
        633825300114114700748351602688),
    (((-20732073) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02702MinusMidpointP002Radius2558 : ℝ := ((2199023410101 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP002RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP002Factor2558
        batchC02702MinusMidpointP002Center2558) =
        batchC02702MinusMidpointP002Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP002RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP002Rounded2558‖ ≤
          batchC02702MinusMidpointP002Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP002Factor2558
      batchC02702MinusMidpointP002Center2558)
  rw [batchC02702MinusMidpointP002RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP002Factor2558 * embedPair2542
        batchC02702MinusMidpointP002Center2558)
    (embedPair2542 batchC02702MinusMidpointP002Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP002DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP002Factor2558,
      batchC02702MinusMidpointP002Error2558, rounding2542,
      batchC02702MinusMidpointP002Radius2558]

theorem batchC02702MinusMidpointP002DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP002Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP002RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP002Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP002Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP002Rounded2558]

def batchC02702MinusMidpointP003Rounded2558 : RatPair2542 :=
  (((332041375062099 : ℚ) /
        1267650600228229401496703205376),
    ((135779314611771 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02702MinusMidpointP003Radius2558 : ℝ := ((988460041035 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02702MinusMidpointP003RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP003Factor2558
        batchC02702MinusMidpointP003Center2558) =
        batchC02702MinusMidpointP003Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP003RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP003Rounded2558‖ ≤
          batchC02702MinusMidpointP003Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP003Factor2558
      batchC02702MinusMidpointP003Center2558)
  rw [batchC02702MinusMidpointP003RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP003Factor2558 * embedPair2542
        batchC02702MinusMidpointP003Center2558)
    (embedPair2542 batchC02702MinusMidpointP003Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP003DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP003Factor2558,
      batchC02702MinusMidpointP003Error2558, rounding2542,
      batchC02702MinusMidpointP003Radius2558]

theorem batchC02702MinusMidpointP003DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP003Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP003RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP003Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP003Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP003Rounded2558]

def batchC02702MinusMidpointP004Rounded2558 : RatPair2542 :=
  (((60650623193939305 : ℚ) /
        633825300114114700748351602688),
    (((-107308581909215647) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02702MinusMidpointP004Radius2558 : ℝ := ((351471856202737 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02702MinusMidpointP004RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP004Factor2558
        batchC02702MinusMidpointP004Center2558) =
        batchC02702MinusMidpointP004Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP004RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP004Rounded2558‖ ≤
          batchC02702MinusMidpointP004Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP004Factor2558
      batchC02702MinusMidpointP004Center2558)
  rw [batchC02702MinusMidpointP004RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP004Factor2558 * embedPair2542
        batchC02702MinusMidpointP004Center2558)
    (embedPair2542 batchC02702MinusMidpointP004Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP004DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP004Factor2558,
      batchC02702MinusMidpointP004Error2558, rounding2542,
      batchC02702MinusMidpointP004Radius2558]

theorem batchC02702MinusMidpointP004DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP004Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP004RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP004Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP004Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP004Rounded2558]

def batchC02702MinusMidpointP005Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP005Radius2558 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02702MinusMidpointP005RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP005Factor2558
        batchC02702MinusMidpointP005Center2558) =
        batchC02702MinusMidpointP005Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP005RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP005Rounded2558‖ ≤
          batchC02702MinusMidpointP005Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP005Factor2558
      batchC02702MinusMidpointP005Center2558)
  rw [batchC02702MinusMidpointP005RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP005Factor2558 * embedPair2542
        batchC02702MinusMidpointP005Center2558)
    (embedPair2542 batchC02702MinusMidpointP005Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP005DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP005Factor2558,
      batchC02702MinusMidpointP005Error2558, rounding2542,
      batchC02702MinusMidpointP005Radius2558]

theorem batchC02702MinusMidpointP005DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP005Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP005RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP005Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP005Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP005Rounded2558]

def batchC02702MinusMidpointP006Rounded2558 : RatPair2542 :=
  (((105 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP006Radius2558 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP006RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP006Factor2558
        batchC02702MinusMidpointP006Center2558) =
        batchC02702MinusMidpointP006Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP006RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP006Rounded2558‖ ≤
          batchC02702MinusMidpointP006Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP006Factor2558
      batchC02702MinusMidpointP006Center2558)
  rw [batchC02702MinusMidpointP006RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP006Factor2558 * embedPair2542
        batchC02702MinusMidpointP006Center2558)
    (embedPair2542 batchC02702MinusMidpointP006Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP006DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP006Factor2558,
      batchC02702MinusMidpointP006Error2558, rounding2542,
      batchC02702MinusMidpointP006Radius2558]

theorem batchC02702MinusMidpointP006DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP006Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP006RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP006Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP006Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP006Rounded2558]

def batchC02702MinusMidpointP007Rounded2558 : RatPair2542 :=
  (((9095605633545 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP007Radius2558 : ℝ := ((137753535255 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem batchC02702MinusMidpointP007RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP007Factor2558
        batchC02702MinusMidpointP007Center2558) =
        batchC02702MinusMidpointP007Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP007RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP007Rounded2558‖ ≤
          batchC02702MinusMidpointP007Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP007Factor2558
      batchC02702MinusMidpointP007Center2558)
  rw [batchC02702MinusMidpointP007RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP007Factor2558 * embedPair2542
        batchC02702MinusMidpointP007Center2558)
    (embedPair2542 batchC02702MinusMidpointP007Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP007DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP007Factor2558,
      batchC02702MinusMidpointP007Error2558, rounding2542,
      batchC02702MinusMidpointP007Radius2558]

theorem batchC02702MinusMidpointP007DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP007Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP007RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP007Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP007Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP007Rounded2558]

def batchC02702MinusMidpointP008Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP008Radius2558 : ℝ := ((1099531261449 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02702MinusMidpointP008RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP008Factor2558
        batchC02702MinusMidpointP008Center2558) =
        batchC02702MinusMidpointP008Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP008RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP008Rounded2558‖ ≤
          batchC02702MinusMidpointP008Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP008Factor2558
      batchC02702MinusMidpointP008Center2558)
  rw [batchC02702MinusMidpointP008RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP008Factor2558 * embedPair2542
        batchC02702MinusMidpointP008Center2558)
    (embedPair2542 batchC02702MinusMidpointP008Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP008DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP008Factor2558,
      batchC02702MinusMidpointP008Error2558, rounding2542,
      batchC02702MinusMidpointP008Radius2558]

theorem batchC02702MinusMidpointP008DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP008Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP008RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP008Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP008Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP008Rounded2558]

def batchC02702MinusMidpointP009Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP009Radius2558 : ℝ := ((2199062523017 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP009RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP009Factor2558
        batchC02702MinusMidpointP009Center2558) =
        batchC02702MinusMidpointP009Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP009RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP009Rounded2558‖ ≤
          batchC02702MinusMidpointP009Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP009Factor2558
      batchC02702MinusMidpointP009Center2558)
  rw [batchC02702MinusMidpointP009RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP009Factor2558 * embedPair2542
        batchC02702MinusMidpointP009Center2558)
    (embedPair2542 batchC02702MinusMidpointP009Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP009DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP009Factor2558,
      batchC02702MinusMidpointP009Error2558, rounding2542,
      batchC02702MinusMidpointP009Radius2558]

theorem batchC02702MinusMidpointP009DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP009Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP009RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP009Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP009Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP009Rounded2558]

def batchC02702MinusMidpointP010Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP010Radius2558 : ℝ := ((1099531261543 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02702MinusMidpointP010RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP010Factor2558
        batchC02702MinusMidpointP010Center2558) =
        batchC02702MinusMidpointP010Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP010RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP010Rounded2558‖ ≤
          batchC02702MinusMidpointP010Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP010Factor2558
      batchC02702MinusMidpointP010Center2558)
  rw [batchC02702MinusMidpointP010RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP010Factor2558 * embedPair2542
        batchC02702MinusMidpointP010Center2558)
    (embedPair2542 batchC02702MinusMidpointP010Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP010DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP010Factor2558,
      batchC02702MinusMidpointP010Error2558, rounding2542,
      batchC02702MinusMidpointP010Radius2558]

theorem batchC02702MinusMidpointP010DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP010Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP010RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP010Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP010Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP010Rounded2558]

def batchC02702MinusMidpointP011Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP011Radius2558 : ℝ := ((2199062523133 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP011RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP011Factor2558
        batchC02702MinusMidpointP011Center2558) =
        batchC02702MinusMidpointP011Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP011RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP011Rounded2558‖ ≤
          batchC02702MinusMidpointP011Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP011Factor2558
      batchC02702MinusMidpointP011Center2558)
  rw [batchC02702MinusMidpointP011RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP011Factor2558 * embedPair2542
        batchC02702MinusMidpointP011Center2558)
    (embedPair2542 batchC02702MinusMidpointP011Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP011DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP011Factor2558,
      batchC02702MinusMidpointP011Error2558, rounding2542,
      batchC02702MinusMidpointP011Radius2558]

theorem batchC02702MinusMidpointP011DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP011Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP011RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP011Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP011Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP011Rounded2558]

def batchC02702MinusMidpointP012Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP012Radius2558 : ℝ := ((549765630795 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02702MinusMidpointP012RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP012Factor2558
        batchC02702MinusMidpointP012Center2558) =
        batchC02702MinusMidpointP012Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP012RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP012Rounded2558‖ ≤
          batchC02702MinusMidpointP012Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP012Factor2558
      batchC02702MinusMidpointP012Center2558)
  rw [batchC02702MinusMidpointP012RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP012Factor2558 * embedPair2542
        batchC02702MinusMidpointP012Center2558)
    (embedPair2542 batchC02702MinusMidpointP012Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP012DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP012Factor2558,
      batchC02702MinusMidpointP012Error2558, rounding2542,
      batchC02702MinusMidpointP012Radius2558]

theorem batchC02702MinusMidpointP012DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP012Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP012RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP012Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP012Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP012Rounded2558]

def batchC02702MinusMidpointP013Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP013Radius2558 : ℝ := ((274882815403 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02702MinusMidpointP013RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP013Factor2558
        batchC02702MinusMidpointP013Center2558) =
        batchC02702MinusMidpointP013Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP013RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP013Rounded2558‖ ≤
          batchC02702MinusMidpointP013Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP013Factor2558
      batchC02702MinusMidpointP013Center2558)
  rw [batchC02702MinusMidpointP013RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP013Factor2558 * embedPair2542
        batchC02702MinusMidpointP013Center2558)
    (embedPair2542 batchC02702MinusMidpointP013Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP013DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP013Factor2558,
      batchC02702MinusMidpointP013Error2558, rounding2542,
      batchC02702MinusMidpointP013Radius2558]

theorem batchC02702MinusMidpointP013DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP013Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP013RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP013Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP013Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP013Rounded2558]

def batchC02702MinusMidpointP014Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP014Radius2558 : ℝ := ((274882815413 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02702MinusMidpointP014RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP014Factor2558
        batchC02702MinusMidpointP014Center2558) =
        batchC02702MinusMidpointP014Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP014RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP014Rounded2558‖ ≤
          batchC02702MinusMidpointP014Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP014Factor2558
      batchC02702MinusMidpointP014Center2558)
  rw [batchC02702MinusMidpointP014RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP014Factor2558 * embedPair2542
        batchC02702MinusMidpointP014Center2558)
    (embedPair2542 batchC02702MinusMidpointP014Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP014DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP014Factor2558,
      batchC02702MinusMidpointP014Error2558, rounding2542,
      batchC02702MinusMidpointP014Radius2558]

theorem batchC02702MinusMidpointP014DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP014Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP014RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP014Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP014Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP014Rounded2558]

def batchC02702MinusMidpointP015Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP015Radius2558 : ℝ := ((1099531261681 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02702MinusMidpointP015RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP015Factor2558
        batchC02702MinusMidpointP015Center2558) =
        batchC02702MinusMidpointP015Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP015RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP015Rounded2558‖ ≤
          batchC02702MinusMidpointP015Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP015Factor2558
      batchC02702MinusMidpointP015Center2558)
  rw [batchC02702MinusMidpointP015RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP015Factor2558 * embedPair2542
        batchC02702MinusMidpointP015Center2558)
    (embedPair2542 batchC02702MinusMidpointP015Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP015DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP015Factor2558,
      batchC02702MinusMidpointP015Error2558, rounding2542,
      batchC02702MinusMidpointP015Radius2558]

theorem batchC02702MinusMidpointP015DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP015Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP015RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP015Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP015Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP015Rounded2558]

def batchC02702MinusMidpointP016Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP016Radius2558 : ℝ := ((549765630851 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02702MinusMidpointP016RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP016Factor2558
        batchC02702MinusMidpointP016Center2558) =
        batchC02702MinusMidpointP016Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP016RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP016Rounded2558‖ ≤
          batchC02702MinusMidpointP016Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP016Factor2558
      batchC02702MinusMidpointP016Center2558)
  rw [batchC02702MinusMidpointP016RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP016Factor2558 * embedPair2542
        batchC02702MinusMidpointP016Center2558)
    (embedPair2542 batchC02702MinusMidpointP016Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP016DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP016Factor2558,
      batchC02702MinusMidpointP016Error2558, rounding2542,
      batchC02702MinusMidpointP016Radius2558]

theorem batchC02702MinusMidpointP016DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP016Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP016RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP016Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP016Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP016Rounded2558]

def batchC02702MinusMidpointP017Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP017Radius2558 : ℝ := ((549765630871 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02702MinusMidpointP017RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP017Factor2558
        batchC02702MinusMidpointP017Center2558) =
        batchC02702MinusMidpointP017Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP017RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP017Rounded2558‖ ≤
          batchC02702MinusMidpointP017Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP017Factor2558
      batchC02702MinusMidpointP017Center2558)
  rw [batchC02702MinusMidpointP017RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP017Factor2558 * embedPair2542
        batchC02702MinusMidpointP017Center2558)
    (embedPair2542 batchC02702MinusMidpointP017Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP017DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP017Factor2558,
      batchC02702MinusMidpointP017Error2558, rounding2542,
      batchC02702MinusMidpointP017Radius2558]

theorem batchC02702MinusMidpointP017DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP017Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP017RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP017Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP017Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP017Rounded2558]

def batchC02702MinusMidpointP018Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP018Radius2558 : ℝ := ((2199062523515 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP018RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP018Factor2558
        batchC02702MinusMidpointP018Center2558) =
        batchC02702MinusMidpointP018Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP018RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP018Rounded2558‖ ≤
          batchC02702MinusMidpointP018Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP018Factor2558
      batchC02702MinusMidpointP018Center2558)
  rw [batchC02702MinusMidpointP018RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP018Factor2558 * embedPair2542
        batchC02702MinusMidpointP018Center2558)
    (embedPair2542 batchC02702MinusMidpointP018Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP018DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP018Factor2558,
      batchC02702MinusMidpointP018Error2558, rounding2542,
      batchC02702MinusMidpointP018Radius2558]

theorem batchC02702MinusMidpointP018DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP018Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP018RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP018Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP018Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP018Rounded2558]

def batchC02702MinusMidpointP019Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP019Radius2558 : ℝ := ((1099531261785 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02702MinusMidpointP019RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP019Factor2558
        batchC02702MinusMidpointP019Center2558) =
        batchC02702MinusMidpointP019Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP019RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP019Rounded2558‖ ≤
          batchC02702MinusMidpointP019Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP019Factor2558
      batchC02702MinusMidpointP019Center2558)
  rw [batchC02702MinusMidpointP019RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP019Factor2558 * embedPair2542
        batchC02702MinusMidpointP019Center2558)
    (embedPair2542 batchC02702MinusMidpointP019Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP019DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP019Factor2558,
      batchC02702MinusMidpointP019Error2558, rounding2542,
      batchC02702MinusMidpointP019Radius2558]

theorem batchC02702MinusMidpointP019DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP019Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP019RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP019Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP019Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP019Rounded2558]

def batchC02702MinusMidpointP020Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP020Radius2558 : ℝ := ((2199062523631 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP020RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP020Factor2558
        batchC02702MinusMidpointP020Center2558) =
        batchC02702MinusMidpointP020Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP020RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP020Rounded2558‖ ≤
          batchC02702MinusMidpointP020Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP020Factor2558
      batchC02702MinusMidpointP020Center2558)
  rw [batchC02702MinusMidpointP020RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP020Factor2558 * embedPair2542
        batchC02702MinusMidpointP020Center2558)
    (embedPair2542 batchC02702MinusMidpointP020Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP020DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP020Factor2558,
      batchC02702MinusMidpointP020Error2558, rounding2542,
      batchC02702MinusMidpointP020Radius2558]

theorem batchC02702MinusMidpointP020DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP020Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP020RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP020Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP020Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP020Rounded2558]

def batchC02702MinusMidpointP021Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP021Radius2558 : ℝ := ((2199062523681 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP021RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP021Factor2558
        batchC02702MinusMidpointP021Center2558) =
        batchC02702MinusMidpointP021Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP021RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP021Rounded2558‖ ≤
          batchC02702MinusMidpointP021Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP021Factor2558
      batchC02702MinusMidpointP021Center2558)
  rw [batchC02702MinusMidpointP021RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP021Factor2558 * embedPair2542
        batchC02702MinusMidpointP021Center2558)
    (embedPair2542 batchC02702MinusMidpointP021Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP021DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP021Factor2558,
      batchC02702MinusMidpointP021Error2558, rounding2542,
      batchC02702MinusMidpointP021Radius2558]

theorem batchC02702MinusMidpointP021DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP021Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP021RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP021Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP021Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP021Rounded2558]

def batchC02702MinusMidpointP022Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP022Radius2558 : ℝ := ((2199062523707 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP022RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP022Factor2558
        batchC02702MinusMidpointP022Center2558) =
        batchC02702MinusMidpointP022Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP022RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP022Rounded2558‖ ≤
          batchC02702MinusMidpointP022Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP022Factor2558
      batchC02702MinusMidpointP022Center2558)
  rw [batchC02702MinusMidpointP022RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP022Factor2558 * embedPair2542
        batchC02702MinusMidpointP022Center2558)
    (embedPair2542 batchC02702MinusMidpointP022Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP022DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP022Factor2558,
      batchC02702MinusMidpointP022Error2558, rounding2542,
      batchC02702MinusMidpointP022Radius2558]

theorem batchC02702MinusMidpointP022DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP022Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP022RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP022Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP022Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP022Rounded2558]

def batchC02702MinusMidpointP023Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP023Radius2558 : ℝ := ((2199062523781 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP023RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP023Factor2558
        batchC02702MinusMidpointP023Center2558) =
        batchC02702MinusMidpointP023Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP023RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP023Rounded2558‖ ≤
          batchC02702MinusMidpointP023Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP023Factor2558
      batchC02702MinusMidpointP023Center2558)
  rw [batchC02702MinusMidpointP023RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP023Factor2558 * embedPair2542
        batchC02702MinusMidpointP023Center2558)
    (embedPair2542 batchC02702MinusMidpointP023Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP023DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP023Factor2558,
      batchC02702MinusMidpointP023Error2558, rounding2542,
      batchC02702MinusMidpointP023Radius2558]

theorem batchC02702MinusMidpointP023DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP023Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP023RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP023Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP023Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP023Rounded2558]

def batchC02702MinusMidpointP024Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP024Radius2558 : ℝ := ((2199062523815 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP024RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP024Factor2558
        batchC02702MinusMidpointP024Center2558) =
        batchC02702MinusMidpointP024Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP024RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP024Rounded2558‖ ≤
          batchC02702MinusMidpointP024Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP024Factor2558
      batchC02702MinusMidpointP024Center2558)
  rw [batchC02702MinusMidpointP024RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP024Factor2558 * embedPair2542
        batchC02702MinusMidpointP024Center2558)
    (embedPair2542 batchC02702MinusMidpointP024Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP024DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP024Factor2558,
      batchC02702MinusMidpointP024Error2558, rounding2542,
      batchC02702MinusMidpointP024Radius2558]

theorem batchC02702MinusMidpointP024DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP024Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP024RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP024Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP024Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP024Rounded2558]

def batchC02702MinusMidpointP025Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP025Radius2558 : ℝ := ((2199062523857 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP025RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP025Factor2558
        batchC02702MinusMidpointP025Center2558) =
        batchC02702MinusMidpointP025Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP025RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP025Rounded2558‖ ≤
          batchC02702MinusMidpointP025Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP025Factor2558
      batchC02702MinusMidpointP025Center2558)
  rw [batchC02702MinusMidpointP025RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP025Factor2558 * embedPair2542
        batchC02702MinusMidpointP025Center2558)
    (embedPair2542 batchC02702MinusMidpointP025Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP025DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP025Factor2558,
      batchC02702MinusMidpointP025Error2558, rounding2542,
      batchC02702MinusMidpointP025Radius2558]

theorem batchC02702MinusMidpointP025DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP025Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP025RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP025Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP025Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP025Rounded2558]

def batchC02702MinusMidpointP026Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP026Radius2558 : ℝ := ((2199062523901 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP026RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP026Factor2558
        batchC02702MinusMidpointP026Center2558) =
        batchC02702MinusMidpointP026Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP026RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP026Rounded2558‖ ≤
          batchC02702MinusMidpointP026Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP026Factor2558
      batchC02702MinusMidpointP026Center2558)
  rw [batchC02702MinusMidpointP026RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP026Factor2558 * embedPair2542
        batchC02702MinusMidpointP026Center2558)
    (embedPair2542 batchC02702MinusMidpointP026Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP026DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP026Factor2558,
      batchC02702MinusMidpointP026Error2558, rounding2542,
      batchC02702MinusMidpointP026Radius2558]

theorem batchC02702MinusMidpointP026DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP026Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP026RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP026Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP026Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP026Rounded2558]

def batchC02702MinusMidpointP027Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP027Radius2558 : ℝ := ((549765630991 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02702MinusMidpointP027RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP027Factor2558
        batchC02702MinusMidpointP027Center2558) =
        batchC02702MinusMidpointP027Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP027RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP027Rounded2558‖ ≤
          batchC02702MinusMidpointP027Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP027Factor2558
      batchC02702MinusMidpointP027Center2558)
  rw [batchC02702MinusMidpointP027RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP027Factor2558 * embedPair2542
        batchC02702MinusMidpointP027Center2558)
    (embedPair2542 batchC02702MinusMidpointP027Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP027DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP027Factor2558,
      batchC02702MinusMidpointP027Error2558, rounding2542,
      batchC02702MinusMidpointP027Radius2558]

theorem batchC02702MinusMidpointP027DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP027Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP027RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP027Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP027Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP027Rounded2558]

def batchC02702MinusMidpointP028Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP028Radius2558 : ℝ := ((2199062523989 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP028RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP028Factor2558
        batchC02702MinusMidpointP028Center2558) =
        batchC02702MinusMidpointP028Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP028RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP028Rounded2558‖ ≤
          batchC02702MinusMidpointP028Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP028Factor2558
      batchC02702MinusMidpointP028Center2558)
  rw [batchC02702MinusMidpointP028RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP028Factor2558 * embedPair2542
        batchC02702MinusMidpointP028Center2558)
    (embedPair2542 batchC02702MinusMidpointP028Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP028DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP028Factor2558,
      batchC02702MinusMidpointP028Error2558, rounding2542,
      batchC02702MinusMidpointP028Radius2558]

theorem batchC02702MinusMidpointP028DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP028Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP028RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP028Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP028Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP028Rounded2558]

def batchC02702MinusMidpointP029Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP029Radius2558 : ℝ := ((2199062524027 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02702MinusMidpointP029RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02702MinusMidpointP029Factor2558
        batchC02702MinusMidpointP029Center2558) =
        batchC02702MinusMidpointP029Rounded2558 := by
  cbv

theorem batchC02702MinusMidpointP029RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP029Rounded2558‖ ≤
          batchC02702MinusMidpointP029Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02702MinusMidpointP029Factor2558
      batchC02702MinusMidpointP029Center2558)
  rw [batchC02702MinusMidpointP029RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP029Factor2558 * embedPair2542
        batchC02702MinusMidpointP029Center2558)
    (embedPair2542 batchC02702MinusMidpointP029Rounded2558)).trans (add_le_add
        batchC02702MinusMidpointP029DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02702MinusMidpointP029Factor2558,
      batchC02702MinusMidpointP029Error2558, rounding2542,
      batchC02702MinusMidpointP029Radius2558]

theorem batchC02702MinusMidpointP029DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02702MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02702MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02702MinusMidpointPosition2558)
    (embedPair2542 batchC02702MinusMidpointP029Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02702MinusMidpointP029RoundedError2558
      (embedPair_magnitude2542
      batchC02702MinusMidpointP029Rounded2558))
  apply h'.trans
  norm_num [batchC02702MinusMidpointP029Radius2558, pairMagnitude2542,
      batchC02702MinusMidpointP029Rounded2558]

noncomputable def batchC02702MinusSignedMidpointValue2558 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchC02702MinusMidpointP000Rounded2558
  | 1 => embedPair2542 batchC02702MinusMidpointP001Rounded2558
  | 2 => embedPair2542 batchC02702MinusMidpointP002Rounded2558
  | 3 => embedPair2542 batchC02702MinusMidpointP003Rounded2558
  | 4 => embedPair2542 batchC02702MinusMidpointP004Rounded2558
  | 5 => embedPair2542 batchC02702MinusMidpointP005Rounded2558
  | 6 => embedPair2542 batchC02702MinusMidpointP006Rounded2558
  | 7 => embedPair2542 batchC02702MinusMidpointP007Rounded2558
  | 8 => embedPair2542 batchC02702MinusMidpointP008Rounded2558
  | 9 => embedPair2542 batchC02702MinusMidpointP009Rounded2558
  | 10 => embedPair2542 batchC02702MinusMidpointP010Rounded2558
  | 11 => embedPair2542 batchC02702MinusMidpointP011Rounded2558
  | 12 => embedPair2542 batchC02702MinusMidpointP012Rounded2558
  | 13 => embedPair2542 batchC02702MinusMidpointP013Rounded2558
  | 14 => embedPair2542 batchC02702MinusMidpointP014Rounded2558
  | 15 => embedPair2542 batchC02702MinusMidpointP015Rounded2558
  | 16 => embedPair2542 batchC02702MinusMidpointP016Rounded2558
  | 17 => embedPair2542 batchC02702MinusMidpointP017Rounded2558
  | 18 => embedPair2542 batchC02702MinusMidpointP018Rounded2558
  | 19 => embedPair2542 batchC02702MinusMidpointP019Rounded2558
  | 20 => embedPair2542 batchC02702MinusMidpointP020Rounded2558
  | 21 => embedPair2542 batchC02702MinusMidpointP021Rounded2558
  | 22 => embedPair2542 batchC02702MinusMidpointP022Rounded2558
  | 23 => embedPair2542 batchC02702MinusMidpointP023Rounded2558
  | 24 => embedPair2542 batchC02702MinusMidpointP024Rounded2558
  | 25 => embedPair2542 batchC02702MinusMidpointP025Rounded2558
  | 26 => embedPair2542 batchC02702MinusMidpointP026Rounded2558
  | 27 => embedPair2542 batchC02702MinusMidpointP027Rounded2558
  | 28 => embedPair2542 batchC02702MinusMidpointP028Rounded2558
  | 29 => embedPair2542 batchC02702MinusMidpointP029Rounded2558
  | _ => 0

noncomputable def batchC02702MinusSignedMidpointError2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02702MinusMidpointP000Radius2558
  | 1 => batchC02702MinusMidpointP001Radius2558
  | 2 => batchC02702MinusMidpointP002Radius2558
  | 3 => batchC02702MinusMidpointP003Radius2558
  | 4 => batchC02702MinusMidpointP004Radius2558
  | 5 => batchC02702MinusMidpointP005Radius2558
  | 6 => batchC02702MinusMidpointP006Radius2558
  | 7 => batchC02702MinusMidpointP007Radius2558
  | 8 => batchC02702MinusMidpointP008Radius2558
  | 9 => batchC02702MinusMidpointP009Radius2558
  | 10 => batchC02702MinusMidpointP010Radius2558
  | 11 => batchC02702MinusMidpointP011Radius2558
  | 12 => batchC02702MinusMidpointP012Radius2558
  | 13 => batchC02702MinusMidpointP013Radius2558
  | 14 => batchC02702MinusMidpointP014Radius2558
  | 15 => batchC02702MinusMidpointP015Radius2558
  | 16 => batchC02702MinusMidpointP016Radius2558
  | 17 => batchC02702MinusMidpointP017Radius2558
  | 18 => batchC02702MinusMidpointP018Radius2558
  | 19 => batchC02702MinusMidpointP019Radius2558
  | 20 => batchC02702MinusMidpointP020Radius2558
  | 21 => batchC02702MinusMidpointP021Radius2558
  | 22 => batchC02702MinusMidpointP022Radius2558
  | 23 => batchC02702MinusMidpointP023Radius2558
  | 24 => batchC02702MinusMidpointP024Radius2558
  | 25 => batchC02702MinusMidpointP025Radius2558
  | 26 => batchC02702MinusMidpointP026Radius2558
  | 27 => batchC02702MinusMidpointP027Radius2558
  | 28 => batchC02702MinusMidpointP028Radius2558
  | 29 => batchC02702MinusMidpointP029Radius2558
  | _ => 0

theorem batchC02702MinusSignedMidpointExpError2558 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02702MinusMidpointPosition2558 -
        batchC02702MinusSignedMidpointValue2558 i‖ ≤ batchC02702MinusSignedMidpointError2558 i :=
            by
  fin_cases i
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP000RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP001RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP002RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP003RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP004RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP005RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP006RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP007RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP008RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP009RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP010RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP011RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP012RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP013RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP014RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP015RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP016RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP017RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP018RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP019RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP020RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP021RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP022RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP023RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP024RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP025RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP026RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP027RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP028RoundedError2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP029RoundedError2558

theorem batchC02702MinusSignedMidpointUnitNorm2558 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02702MinusMidpointPosition2558‖ ≤ 1
        := by
  fin_cases i
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP000DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP001DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP002DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP003DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP004DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP005DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP006DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP007DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP008DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP009DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP010DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP011DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP012DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP013DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP014DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP015DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP016DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP017DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP018DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP019DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP020DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP021DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP022DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP023DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP024DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP025DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP026DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP027DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP028DerivativeNorm2558
  · simpa only [batchC02702MinusSignedMidpointValue2558, batchC02702MinusSignedMidpointError2558]
      using
      batchC02702MinusMidpointP029DerivativeNorm2558

noncomputable def batchC02702MinusSignedMidpointSum2558 : ℂ := ⟨(((-(((160767 * 10^40
        + 7453597288582918812275201430655032222663) * 10^40
        + 1376090479763068189614379347195481536412) * 10^40
        + 6512436049539891521750994832235224801201)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216)),
    (((-(((7009 * 10^40
        + 9836531774989560092975525777007510059295) * 10^40
        + 4741951220094010464679248005000817598999) * 10^40
        + 9976185447339878394135367590501286687845)) : ℝ) /
        (((21661481 * 10^40
        + 9853188660904563608136178414330971646513) * 10^40
        + 7356699351937172355172896723145017999980) * 10^40
        + 47688590453885868835635965404913860608))⟩

noncomputable def batchC02702MinusSignedMidpointUpper2558 : ℝ := ((37251 : ℝ) /
        10000000)

theorem batchC02702MinusSignedMidpointSum_eq2558 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02702MinusSignedMidpointValue2558 i) =
      batchC02702MinusSignedMidpointSum2558 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
        batchC02702MinusSignedMidpointValue2558,
      batchC02702MinusSignedMidpointSum2558, embedPair2542,
          batchC02702MinusMidpointP000Rounded2558,
      batchC02702MinusMidpointP001Rounded2558,
      batchC02702MinusMidpointP002Rounded2558,
      batchC02702MinusMidpointP003Rounded2558,
      batchC02702MinusMidpointP004Rounded2558,
      batchC02702MinusMidpointP005Rounded2558,
      batchC02702MinusMidpointP006Rounded2558,
      batchC02702MinusMidpointP007Rounded2558,
      batchC02702MinusMidpointP008Rounded2558,
      batchC02702MinusMidpointP009Rounded2558,
      batchC02702MinusMidpointP010Rounded2558,
      batchC02702MinusMidpointP011Rounded2558,
      batchC02702MinusMidpointP012Rounded2558,
      batchC02702MinusMidpointP013Rounded2558,
      batchC02702MinusMidpointP014Rounded2558,
      batchC02702MinusMidpointP015Rounded2558,
      batchC02702MinusMidpointP016Rounded2558,
      batchC02702MinusMidpointP017Rounded2558,
      batchC02702MinusMidpointP018Rounded2558,
      batchC02702MinusMidpointP019Rounded2558,
      batchC02702MinusMidpointP020Rounded2558,
      batchC02702MinusMidpointP021Rounded2558,
      batchC02702MinusMidpointP022Rounded2558,
      batchC02702MinusMidpointP023Rounded2558,
      batchC02702MinusMidpointP024Rounded2558,
      batchC02702MinusMidpointP025Rounded2558,
      batchC02702MinusMidpointP026Rounded2558,
      batchC02702MinusMidpointP027Rounded2558,
      batchC02702MinusMidpointP028Rounded2558,
      batchC02702MinusMidpointP029Rounded2558, Complex.mul_re, Complex.mul_im]

theorem batchC02702MinusSignedMidpointSum_norm2558 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02702MinusSignedMidpointValue2558 i‖ ≤
        ((149 : ℝ) /
        40000) := by
  rw [batchC02702MinusSignedMidpointSum_eq2558]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchC02702MinusSignedMidpointSum2558]

theorem batchC02702MinusSignedMidpointCharge2558 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchC02702MinusSignedMidpointError2558 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
      batchC02702MinusSignedMidpointError2558,
      batchC02702MinusMidpointP000Radius2558,
      batchC02702MinusMidpointP001Radius2558,
      batchC02702MinusMidpointP002Radius2558,
      batchC02702MinusMidpointP003Radius2558,
      batchC02702MinusMidpointP004Radius2558,
      batchC02702MinusMidpointP005Radius2558,
      batchC02702MinusMidpointP006Radius2558,
      batchC02702MinusMidpointP007Radius2558,
      batchC02702MinusMidpointP008Radius2558,
      batchC02702MinusMidpointP009Radius2558,
      batchC02702MinusMidpointP010Radius2558,
      batchC02702MinusMidpointP011Radius2558,
      batchC02702MinusMidpointP012Radius2558,
      batchC02702MinusMidpointP013Radius2558,
      batchC02702MinusMidpointP014Radius2558,
      batchC02702MinusMidpointP015Radius2558,
      batchC02702MinusMidpointP016Radius2558,
      batchC02702MinusMidpointP017Radius2558,
      batchC02702MinusMidpointP018Radius2558,
      batchC02702MinusMidpointP019Radius2558,
      batchC02702MinusMidpointP020Radius2558,
      batchC02702MinusMidpointP021Radius2558,
      batchC02702MinusMidpointP022Radius2558,
      batchC02702MinusMidpointP023Radius2558,
      batchC02702MinusMidpointP024Radius2558,
      batchC02702MinusMidpointP025Radius2558,
      batchC02702MinusMidpointP026Radius2558,
      batchC02702MinusMidpointP027Radius2558,
      batchC02702MinusMidpointP028Radius2558,
      batchC02702MinusMidpointP029Radius2558]

theorem batchC02702MinusSignedMidpointUpper_le2558 :
    signedJetUpper2539 2 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchC02702MinusMidpointPosition2558 ≤
          batchC02702MinusSignedMidpointUpper2558 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02702MinusMidpointPosition2558‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02702MinusSignedMidpointValue2558 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchC02702MinusSignedMidpointError2558 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (batchC02702MinusSignedMidpointExpError2558 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02702MinusMidpointPosition2558‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchC02702MinusSignedMidpointUnitNorm2558 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02702MinusMidpointPosition2558‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchC02702MinusSignedMidpointUpper2558
  linarith [batchC02702MinusSignedMidpointSum_norm2558, batchC02702MinusSignedMidpointCharge2558]

theorem batchC02702MinusPhysicalSecond2558 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        batchC02702MinusMidpointPosition2558‖ ≤
      batchC02702MinusSignedMidpointUpper2558 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchC02702MinusMidpointPosition2558
  exact h.trans batchC02702MinusSignedMidpointUpper_le2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02702MinusSignedMidpointExpError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusSignedMidpointSum_eq2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusSignedMidpointCharge2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusSignedMidpointUpper_le2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusPhysicalSecond2558
