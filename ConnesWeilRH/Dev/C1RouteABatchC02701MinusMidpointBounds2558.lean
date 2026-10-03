import ConnesWeilRH.Dev.C1RouteABatchC02701MinusMidpoint2558

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem batchC02701MinusMidpoint_triangle2558 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def batchC02701MinusMidpointP000Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP000Radius2558 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02701MinusMidpointP000RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP000Factor2558
        batchC02701MinusMidpointP000Center2558) =
        batchC02701MinusMidpointP000Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP000RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP000Rounded2558‖ ≤
          batchC02701MinusMidpointP000Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP000Factor2558
      batchC02701MinusMidpointP000Center2558)
  rw [batchC02701MinusMidpointP000RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP000Factor2558 * embedPair2542
        batchC02701MinusMidpointP000Center2558)
    (embedPair2542 batchC02701MinusMidpointP000Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP000DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP000Factor2558,
      batchC02701MinusMidpointP000Error2558, rounding2542,
      batchC02701MinusMidpointP000Radius2558]

theorem batchC02701MinusMidpointP000DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP000Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP000RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP000Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP000Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP000Rounded2558]

def batchC02701MinusMidpointP001Rounded2558 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP001Radius2558 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02701MinusMidpointP001RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP001Factor2558
        batchC02701MinusMidpointP001Center2558) =
        batchC02701MinusMidpointP001Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP001RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP001Rounded2558‖ ≤
          batchC02701MinusMidpointP001Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP001Factor2558
      batchC02701MinusMidpointP001Center2558)
  rw [batchC02701MinusMidpointP001RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP001Factor2558 * embedPair2542
        batchC02701MinusMidpointP001Center2558)
    (embedPair2542 batchC02701MinusMidpointP001Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP001DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP001Factor2558,
      batchC02701MinusMidpointP001Error2558, rounding2542,
      batchC02701MinusMidpointP001Radius2558]

theorem batchC02701MinusMidpointP001DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP001Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP001RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP001Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP001Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP001Rounded2558]

def batchC02701MinusMidpointP002Rounded2558 : RatPair2542 :=
  (((32161535 : ℚ) /
        1267650600228229401496703205376),
    (((-21426725) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02701MinusMidpointP002Radius2558 : ℝ := ((2199023401881 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02701MinusMidpointP002RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP002Factor2558
        batchC02701MinusMidpointP002Center2558) =
        batchC02701MinusMidpointP002Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP002RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP002Rounded2558‖ ≤
          batchC02701MinusMidpointP002Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP002Factor2558
      batchC02701MinusMidpointP002Center2558)
  rw [batchC02701MinusMidpointP002RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP002Factor2558 * embedPair2542
        batchC02701MinusMidpointP002Center2558)
    (embedPair2542 batchC02701MinusMidpointP002Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP002DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP002Factor2558,
      batchC02701MinusMidpointP002Error2558, rounding2542,
      batchC02701MinusMidpointP002Radius2558]

theorem batchC02701MinusMidpointP002DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP002Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP002RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP002Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP002Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP002Rounded2558]

def batchC02701MinusMidpointP003Rounded2558 : RatPair2542 :=
  (((20793699760847 : ℚ) /
        79228162514264337593543950336),
    ((116620257820633 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02701MinusMidpointP003Radius2558 : ℝ := ((3912682925447 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02701MinusMidpointP003RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP003Factor2558
        batchC02701MinusMidpointP003Center2558) =
        batchC02701MinusMidpointP003Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP003RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP003Rounded2558‖ ≤
          batchC02701MinusMidpointP003Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP003Factor2558
      batchC02701MinusMidpointP003Center2558)
  rw [batchC02701MinusMidpointP003RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP003Factor2558 * embedPair2542
        batchC02701MinusMidpointP003Center2558)
    (embedPair2542 batchC02701MinusMidpointP003Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP003DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP003Factor2558,
      batchC02701MinusMidpointP003Error2558, rounding2542,
      batchC02701MinusMidpointP003Radius2558]

theorem batchC02701MinusMidpointP003DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP003Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP003RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP003Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP003Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP003Rounded2558]

def batchC02701MinusMidpointP004Rounded2558 : RatPair2542 :=
  (((62750675647064755 : ℚ) /
        633825300114114700748351602688),
    (((-25047290589943139) : ℚ) /
        316912650057057350374175801344))

noncomputable def batchC02701MinusMidpointP004Radius2558 : ℝ := ((86581930924447 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02701MinusMidpointP004RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP004Factor2558
        batchC02701MinusMidpointP004Center2558) =
        batchC02701MinusMidpointP004Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP004RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP004Rounded2558‖ ≤
          batchC02701MinusMidpointP004Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP004Factor2558
      batchC02701MinusMidpointP004Center2558)
  rw [batchC02701MinusMidpointP004RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP004Factor2558 * embedPair2542
        batchC02701MinusMidpointP004Center2558)
    (embedPair2542 batchC02701MinusMidpointP004Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP004DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP004Factor2558,
      batchC02701MinusMidpointP004Error2558, rounding2542,
      batchC02701MinusMidpointP004Radius2558]

theorem batchC02701MinusMidpointP004DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP004Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP004RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP004Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP004Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP004Rounded2558]

def batchC02701MinusMidpointP005Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP005Radius2558 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02701MinusMidpointP005RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP005Factor2558
        batchC02701MinusMidpointP005Center2558) =
        batchC02701MinusMidpointP005Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP005RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP005Rounded2558‖ ≤
          batchC02701MinusMidpointP005Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP005Factor2558
      batchC02701MinusMidpointP005Center2558)
  rw [batchC02701MinusMidpointP005RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP005Factor2558 * embedPair2542
        batchC02701MinusMidpointP005Center2558)
    (embedPair2542 batchC02701MinusMidpointP005Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP005DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP005Factor2558,
      batchC02701MinusMidpointP005Error2558, rounding2542,
      batchC02701MinusMidpointP005Radius2558]

theorem batchC02701MinusMidpointP005DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP005Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP005RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP005Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP005Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP005Rounded2558]

def batchC02701MinusMidpointP006Rounded2558 : RatPair2542 :=
  (((3 : ℚ) /
        39614081257132168796771975168),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP006Radius2558 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02701MinusMidpointP006RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP006Factor2558
        batchC02701MinusMidpointP006Center2558) =
        batchC02701MinusMidpointP006Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP006RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP006Rounded2558‖ ≤
          batchC02701MinusMidpointP006Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP006Factor2558
      batchC02701MinusMidpointP006Center2558)
  rw [batchC02701MinusMidpointP006RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP006Factor2558 * embedPair2542
        batchC02701MinusMidpointP006Center2558)
    (embedPair2542 batchC02701MinusMidpointP006Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP006DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP006Factor2558,
      batchC02701MinusMidpointP006Error2558, rounding2542,
      batchC02701MinusMidpointP006Radius2558]

theorem batchC02701MinusMidpointP006DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP006Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP006RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP006Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP006Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP006Rounded2558]

def batchC02701MinusMidpointP007Rounded2558 : RatPair2542 :=
  (((17919443941051 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP007Radius2558 : ℝ := ((2203982738439 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02701MinusMidpointP007RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP007Factor2558
        batchC02701MinusMidpointP007Center2558) =
        batchC02701MinusMidpointP007Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP007RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP007Rounded2558‖ ≤
          batchC02701MinusMidpointP007Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP007Factor2558
      batchC02701MinusMidpointP007Center2558)
  rw [batchC02701MinusMidpointP007RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP007Factor2558 * embedPair2542
        batchC02701MinusMidpointP007Center2558)
    (embedPair2542 batchC02701MinusMidpointP007Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP007DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP007Factor2558,
      batchC02701MinusMidpointP007Error2558, rounding2542,
      batchC02701MinusMidpointP007Radius2558]

theorem batchC02701MinusMidpointP007DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP007Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP007RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP007Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP007Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP007Rounded2558]

def batchC02701MinusMidpointP008Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP008Radius2558 : ℝ := ((549831567975 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02701MinusMidpointP008RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP008Factor2558
        batchC02701MinusMidpointP008Center2558) =
        batchC02701MinusMidpointP008Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP008RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP008Rounded2558‖ ≤
          batchC02701MinusMidpointP008Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP008Factor2558
      batchC02701MinusMidpointP008Center2558)
  rw [batchC02701MinusMidpointP008RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP008Factor2558 * embedPair2542
        batchC02701MinusMidpointP008Center2558)
    (embedPair2542 batchC02701MinusMidpointP008Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP008DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP008Factor2558,
      batchC02701MinusMidpointP008Error2558, rounding2542,
      batchC02701MinusMidpointP008Radius2558]

theorem batchC02701MinusMidpointP008DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP008Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP008RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP008Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP008Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP008Rounded2558]

def batchC02701MinusMidpointP009Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP009Radius2558 : ℝ := ((2199326272231 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02701MinusMidpointP009RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP009Factor2558
        batchC02701MinusMidpointP009Center2558) =
        batchC02701MinusMidpointP009Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP009RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP009Rounded2558‖ ≤
          batchC02701MinusMidpointP009Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP009Factor2558
      batchC02701MinusMidpointP009Center2558)
  rw [batchC02701MinusMidpointP009RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP009Factor2558 * embedPair2542
        batchC02701MinusMidpointP009Center2558)
    (embedPair2542 batchC02701MinusMidpointP009Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP009DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP009Factor2558,
      batchC02701MinusMidpointP009Error2558, rounding2542,
      batchC02701MinusMidpointP009Radius2558]

theorem batchC02701MinusMidpointP009DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 := by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP009Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP009RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP009Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP009Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP009Rounded2558]

def batchC02701MinusMidpointP010Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP010Radius2558 : ℝ := ((2199326272423 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02701MinusMidpointP010RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP010Factor2558
        batchC02701MinusMidpointP010Center2558) =
        batchC02701MinusMidpointP010Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP010RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP010Rounded2558‖ ≤
          batchC02701MinusMidpointP010Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP010Factor2558
      batchC02701MinusMidpointP010Center2558)
  rw [batchC02701MinusMidpointP010RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP010Factor2558 * embedPair2542
        batchC02701MinusMidpointP010Center2558)
    (embedPair2542 batchC02701MinusMidpointP010Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP010DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP010Factor2558,
      batchC02701MinusMidpointP010Error2558, rounding2542,
      batchC02701MinusMidpointP010Radius2558]

theorem batchC02701MinusMidpointP010DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP010Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP010RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP010Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP010Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP010Rounded2558]

def batchC02701MinusMidpointP011Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP011Radius2558 : ℝ := ((2199326272551 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02701MinusMidpointP011RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP011Factor2558
        batchC02701MinusMidpointP011Center2558) =
        batchC02701MinusMidpointP011Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP011RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP011Rounded2558‖ ≤
          batchC02701MinusMidpointP011Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP011Factor2558
      batchC02701MinusMidpointP011Center2558)
  rw [batchC02701MinusMidpointP011RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP011Factor2558 * embedPair2542
        batchC02701MinusMidpointP011Center2558)
    (embedPair2542 batchC02701MinusMidpointP011Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP011DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP011Factor2558,
      batchC02701MinusMidpointP011Error2558, rounding2542,
      batchC02701MinusMidpointP011Radius2558]

theorem batchC02701MinusMidpointP011DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP011Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP011RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP011Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP011Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP011Rounded2558]

def batchC02701MinusMidpointP012Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP012Radius2558 : ℝ := ((549831568171 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02701MinusMidpointP012RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP012Factor2558
        batchC02701MinusMidpointP012Center2558) =
        batchC02701MinusMidpointP012Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP012RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP012Rounded2558‖ ≤
          batchC02701MinusMidpointP012Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP012Factor2558
      batchC02701MinusMidpointP012Center2558)
  rw [batchC02701MinusMidpointP012RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP012Factor2558 * embedPair2542
        batchC02701MinusMidpointP012Center2558)
    (embedPair2542 batchC02701MinusMidpointP012Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP012DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP012Factor2558,
      batchC02701MinusMidpointP012Error2558, rounding2542,
      batchC02701MinusMidpointP012Radius2558]

theorem batchC02701MinusMidpointP012DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP012Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP012RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP012Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP012Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP012Rounded2558]

def batchC02701MinusMidpointP013Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP013Radius2558 : ℝ := ((549831568201 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02701MinusMidpointP013RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP013Factor2558
        batchC02701MinusMidpointP013Center2558) =
        batchC02701MinusMidpointP013Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP013RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP013Rounded2558‖ ≤
          batchC02701MinusMidpointP013Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP013Factor2558
      batchC02701MinusMidpointP013Center2558)
  rw [batchC02701MinusMidpointP013RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP013Factor2558 * embedPair2542
        batchC02701MinusMidpointP013Center2558)
    (embedPair2542 batchC02701MinusMidpointP013Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP013DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP013Factor2558,
      batchC02701MinusMidpointP013Error2558, rounding2542,
      batchC02701MinusMidpointP013Radius2558]

theorem batchC02701MinusMidpointP013DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP013Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP013RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP013Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP013Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP013Rounded2558]

def batchC02701MinusMidpointP014Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP014Radius2558 : ℝ := ((549831568257 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02701MinusMidpointP014RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP014Factor2558
        batchC02701MinusMidpointP014Center2558) =
        batchC02701MinusMidpointP014Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP014RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP014Rounded2558‖ ≤
          batchC02701MinusMidpointP014Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP014Factor2558
      batchC02701MinusMidpointP014Center2558)
  rw [batchC02701MinusMidpointP014RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP014Factor2558 * embedPair2542
        batchC02701MinusMidpointP014Center2558)
    (embedPair2542 batchC02701MinusMidpointP014Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP014DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP014Factor2558,
      batchC02701MinusMidpointP014Error2558, rounding2542,
      batchC02701MinusMidpointP014Radius2558]

theorem batchC02701MinusMidpointP014DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP014Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP014RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP014Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP014Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP014Rounded2558]

def batchC02701MinusMidpointP015Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP015Radius2558 : ℝ := ((549831568297 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02701MinusMidpointP015RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP015Factor2558
        batchC02701MinusMidpointP015Center2558) =
        batchC02701MinusMidpointP015Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP015RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP015Rounded2558‖ ≤
          batchC02701MinusMidpointP015Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP015Factor2558
      batchC02701MinusMidpointP015Center2558)
  rw [batchC02701MinusMidpointP015RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP015Factor2558 * embedPair2542
        batchC02701MinusMidpointP015Center2558)
    (embedPair2542 batchC02701MinusMidpointP015Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP015DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP015Factor2558,
      batchC02701MinusMidpointP015Error2558, rounding2542,
      batchC02701MinusMidpointP015Radius2558]

theorem batchC02701MinusMidpointP015DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP015Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP015RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP015Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP015Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP015Rounded2558]

def batchC02701MinusMidpointP016Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP016Radius2558 : ℝ := ((274915784163 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02701MinusMidpointP016RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP016Factor2558
        batchC02701MinusMidpointP016Center2558) =
        batchC02701MinusMidpointP016Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP016RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP016Rounded2558‖ ≤
          batchC02701MinusMidpointP016Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP016Factor2558
      batchC02701MinusMidpointP016Center2558)
  rw [batchC02701MinusMidpointP016RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP016Factor2558 * embedPair2542
        batchC02701MinusMidpointP016Center2558)
    (embedPair2542 batchC02701MinusMidpointP016Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP016DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP016Factor2558,
      batchC02701MinusMidpointP016Error2558, rounding2542,
      batchC02701MinusMidpointP016Radius2558]

theorem batchC02701MinusMidpointP016DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP016Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP016RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP016Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP016Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP016Rounded2558]

def batchC02701MinusMidpointP017Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP017Radius2558 : ℝ := ((2199326273529 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02701MinusMidpointP017RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP017Factor2558
        batchC02701MinusMidpointP017Center2558) =
        batchC02701MinusMidpointP017Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP017RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP017Rounded2558‖ ≤
          batchC02701MinusMidpointP017Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP017Factor2558
      batchC02701MinusMidpointP017Center2558)
  rw [batchC02701MinusMidpointP017RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP017Factor2558 * embedPair2542
        batchC02701MinusMidpointP017Center2558)
    (embedPair2542 batchC02701MinusMidpointP017Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP017DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP017Factor2558,
      batchC02701MinusMidpointP017Error2558, rounding2542,
      batchC02701MinusMidpointP017Radius2558]

theorem batchC02701MinusMidpointP017DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP017Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP017RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP017Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP017Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP017Rounded2558]

def batchC02701MinusMidpointP018Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP018Radius2558 : ℝ := ((1099663136807 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02701MinusMidpointP018RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP018Factor2558
        batchC02701MinusMidpointP018Center2558) =
        batchC02701MinusMidpointP018Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP018RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP018Rounded2558‖ ≤
          batchC02701MinusMidpointP018Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP018Factor2558
      batchC02701MinusMidpointP018Center2558)
  rw [batchC02701MinusMidpointP018RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP018Factor2558 * embedPair2542
        batchC02701MinusMidpointP018Center2558)
    (embedPair2542 batchC02701MinusMidpointP018Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP018DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP018Factor2558,
      batchC02701MinusMidpointP018Error2558, rounding2542,
      batchC02701MinusMidpointP018Radius2558]

theorem batchC02701MinusMidpointP018DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP018Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP018RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP018Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP018Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP018Rounded2558]

def batchC02701MinusMidpointP019Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP019Radius2558 : ℝ := ((274915784221 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02701MinusMidpointP019RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP019Factor2558
        batchC02701MinusMidpointP019Center2558) =
        batchC02701MinusMidpointP019Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP019RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP019Rounded2558‖ ≤
          batchC02701MinusMidpointP019Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP019Factor2558
      batchC02701MinusMidpointP019Center2558)
  rw [batchC02701MinusMidpointP019RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP019Factor2558 * embedPair2542
        batchC02701MinusMidpointP019Center2558)
    (embedPair2542 batchC02701MinusMidpointP019Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP019DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP019Factor2558,
      batchC02701MinusMidpointP019Error2558, rounding2542,
      batchC02701MinusMidpointP019Radius2558]

theorem batchC02701MinusMidpointP019DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP019Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP019RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP019Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP019Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP019Rounded2558]

def batchC02701MinusMidpointP020Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP020Radius2558 : ℝ := ((2199326273935 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02701MinusMidpointP020RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP020Factor2558
        batchC02701MinusMidpointP020Center2558) =
        batchC02701MinusMidpointP020Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP020RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP020Rounded2558‖ ≤
          batchC02701MinusMidpointP020Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP020Factor2558
      batchC02701MinusMidpointP020Center2558)
  rw [batchC02701MinusMidpointP020RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP020Factor2558 * embedPair2542
        batchC02701MinusMidpointP020Center2558)
    (embedPair2542 batchC02701MinusMidpointP020Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP020DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP020Factor2558,
      batchC02701MinusMidpointP020Error2558, rounding2542,
      batchC02701MinusMidpointP020Radius2558]

theorem batchC02701MinusMidpointP020DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP020Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP020RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP020Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP020Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP020Rounded2558]

def batchC02701MinusMidpointP021Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP021Radius2558 : ℝ := ((1099663137037 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02701MinusMidpointP021RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP021Factor2558
        batchC02701MinusMidpointP021Center2558) =
        batchC02701MinusMidpointP021Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP021RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP021Rounded2558‖ ≤
          batchC02701MinusMidpointP021Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP021Factor2558
      batchC02701MinusMidpointP021Center2558)
  rw [batchC02701MinusMidpointP021RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP021Factor2558 * embedPair2542
        batchC02701MinusMidpointP021Center2558)
    (embedPair2542 batchC02701MinusMidpointP021Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP021DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP021Factor2558,
      batchC02701MinusMidpointP021Error2558, rounding2542,
      batchC02701MinusMidpointP021Radius2558]

theorem batchC02701MinusMidpointP021DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP021Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP021RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP021Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP021Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP021Rounded2558]

def batchC02701MinusMidpointP022Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP022Radius2558 : ℝ := ((1099663137073 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02701MinusMidpointP022RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP022Factor2558
        batchC02701MinusMidpointP022Center2558) =
        batchC02701MinusMidpointP022Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP022RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP022Rounded2558‖ ≤
          batchC02701MinusMidpointP022Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP022Factor2558
      batchC02701MinusMidpointP022Center2558)
  rw [batchC02701MinusMidpointP022RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP022Factor2558 * embedPair2542
        batchC02701MinusMidpointP022Center2558)
    (embedPair2542 batchC02701MinusMidpointP022Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP022DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP022Factor2558,
      batchC02701MinusMidpointP022Error2558, rounding2542,
      batchC02701MinusMidpointP022Radius2558]

theorem batchC02701MinusMidpointP022DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP022Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP022RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP022Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP022Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP022Rounded2558]

def batchC02701MinusMidpointP023Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP023Radius2558 : ℝ := ((2199326274351 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02701MinusMidpointP023RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP023Factor2558
        batchC02701MinusMidpointP023Center2558) =
        batchC02701MinusMidpointP023Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP023RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP023Rounded2558‖ ≤
          batchC02701MinusMidpointP023Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP023Factor2558
      batchC02701MinusMidpointP023Center2558)
  rw [batchC02701MinusMidpointP023RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP023Factor2558 * embedPair2542
        batchC02701MinusMidpointP023Center2558)
    (embedPair2542 batchC02701MinusMidpointP023Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP023DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP023Factor2558,
      batchC02701MinusMidpointP023Error2558, rounding2542,
      batchC02701MinusMidpointP023Radius2558]

theorem batchC02701MinusMidpointP023DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP023Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP023RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP023Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP023Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP023Rounded2558]

def batchC02701MinusMidpointP024Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP024Radius2558 : ℝ := ((1099663137223 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02701MinusMidpointP024RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP024Factor2558
        batchC02701MinusMidpointP024Center2558) =
        batchC02701MinusMidpointP024Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP024RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP024Rounded2558‖ ≤
          batchC02701MinusMidpointP024Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP024Factor2558
      batchC02701MinusMidpointP024Center2558)
  rw [batchC02701MinusMidpointP024RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP024Factor2558 * embedPair2542
        batchC02701MinusMidpointP024Center2558)
    (embedPair2542 batchC02701MinusMidpointP024Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP024DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP024Factor2558,
      batchC02701MinusMidpointP024Error2558, rounding2542,
      batchC02701MinusMidpointP024Radius2558]

theorem batchC02701MinusMidpointP024DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP024Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP024RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP024Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP024Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP024Rounded2558]

def batchC02701MinusMidpointP025Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP025Radius2558 : ℝ := ((2199326274565 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02701MinusMidpointP025RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP025Factor2558
        batchC02701MinusMidpointP025Center2558) =
        batchC02701MinusMidpointP025Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP025RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP025Rounded2558‖ ≤
          batchC02701MinusMidpointP025Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP025Factor2558
      batchC02701MinusMidpointP025Center2558)
  rw [batchC02701MinusMidpointP025RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP025Factor2558 * embedPair2542
        batchC02701MinusMidpointP025Center2558)
    (embedPair2542 batchC02701MinusMidpointP025Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP025DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP025Factor2558,
      batchC02701MinusMidpointP025Error2558, rounding2542,
      batchC02701MinusMidpointP025Radius2558]

theorem batchC02701MinusMidpointP025DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP025Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP025RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP025Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP025Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP025Rounded2558]

def batchC02701MinusMidpointP026Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP026Radius2558 : ℝ := ((1099663137343 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02701MinusMidpointP026RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP026Factor2558
        batchC02701MinusMidpointP026Center2558) =
        batchC02701MinusMidpointP026Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP026RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP026Rounded2558‖ ≤
          batchC02701MinusMidpointP026Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP026Factor2558
      batchC02701MinusMidpointP026Center2558)
  rw [batchC02701MinusMidpointP026RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP026Factor2558 * embedPair2542
        batchC02701MinusMidpointP026Center2558)
    (embedPair2542 batchC02701MinusMidpointP026Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP026DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP026Factor2558,
      batchC02701MinusMidpointP026Error2558, rounding2542,
      batchC02701MinusMidpointP026Radius2558]

theorem batchC02701MinusMidpointP026DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP026Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP026RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP026Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP026Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP026Rounded2558]

def batchC02701MinusMidpointP027Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP027Radius2558 : ℝ := ((2199326274861 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02701MinusMidpointP027RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP027Factor2558
        batchC02701MinusMidpointP027Center2558) =
        batchC02701MinusMidpointP027Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP027RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP027Rounded2558‖ ≤
          batchC02701MinusMidpointP027Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP027Factor2558
      batchC02701MinusMidpointP027Center2558)
  rw [batchC02701MinusMidpointP027RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP027Factor2558 * embedPair2542
        batchC02701MinusMidpointP027Center2558)
    (embedPair2542 batchC02701MinusMidpointP027Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP027DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP027Factor2558,
      batchC02701MinusMidpointP027Error2558, rounding2542,
      batchC02701MinusMidpointP027Radius2558]

theorem batchC02701MinusMidpointP027DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP027Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP027RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP027Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP027Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP027Rounded2558]

def batchC02701MinusMidpointP028Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP028Radius2558 : ℝ := ((1099663137465 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02701MinusMidpointP028RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP028Factor2558
        batchC02701MinusMidpointP028Center2558) =
        batchC02701MinusMidpointP028Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP028RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP028Rounded2558‖ ≤
          batchC02701MinusMidpointP028Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP028Factor2558
      batchC02701MinusMidpointP028Center2558)
  rw [batchC02701MinusMidpointP028RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP028Factor2558 * embedPair2542
        batchC02701MinusMidpointP028Center2558)
    (embedPair2542 batchC02701MinusMidpointP028Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP028DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP028Factor2558,
      batchC02701MinusMidpointP028Error2558, rounding2542,
      batchC02701MinusMidpointP028Radius2558]

theorem batchC02701MinusMidpointP028DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP028Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP028RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP028Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP028Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP028Rounded2558]

def batchC02701MinusMidpointP029Rounded2558 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02701MinusMidpointP029Radius2558 : ℝ := ((2199326275035 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02701MinusMidpointP029RoundCompute2558 :
    pairRound2542 (pairMul2542 batchC02701MinusMidpointP029Factor2558
        batchC02701MinusMidpointP029Center2558) =
        batchC02701MinusMidpointP029Rounded2558 := by
  cbv

theorem batchC02701MinusMidpointP029RoundedError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02701MinusMidpointPosition2558 -
      embedPair2542 batchC02701MinusMidpointP029Rounded2558‖ ≤
          batchC02701MinusMidpointP029Radius2558 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02701MinusMidpointP029Factor2558
      batchC02701MinusMidpointP029Center2558)
  rw [batchC02701MinusMidpointP029RoundCompute2558, embedPair_mul2542] at hr
  have h := (batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP029Factor2558 * embedPair2542
        batchC02701MinusMidpointP029Center2558)
    (embedPair2542 batchC02701MinusMidpointP029Rounded2558)).trans (add_le_add
        batchC02701MinusMidpointP029DerivativeError2558 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02701MinusMidpointP029Factor2558,
      batchC02701MinusMidpointP029Error2558, rounding2542,
      batchC02701MinusMidpointP029Radius2558]

theorem batchC02701MinusMidpointP029DerivativeNorm2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02701MinusMidpointPosition2558‖ ≤ 1 :=
        by
  have h := batchC02701MinusMidpoint_triangle2558
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02701MinusMidpointPosition2558)
    (embedPair2542 batchC02701MinusMidpointP029Rounded2558) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02701MinusMidpointP029RoundedError2558
      (embedPair_magnitude2542
      batchC02701MinusMidpointP029Rounded2558))
  apply h'.trans
  norm_num [batchC02701MinusMidpointP029Radius2558, pairMagnitude2542,
      batchC02701MinusMidpointP029Rounded2558]

noncomputable def batchC02701MinusSignedMidpointValue2558 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchC02701MinusMidpointP000Rounded2558
  | 1 => embedPair2542 batchC02701MinusMidpointP001Rounded2558
  | 2 => embedPair2542 batchC02701MinusMidpointP002Rounded2558
  | 3 => embedPair2542 batchC02701MinusMidpointP003Rounded2558
  | 4 => embedPair2542 batchC02701MinusMidpointP004Rounded2558
  | 5 => embedPair2542 batchC02701MinusMidpointP005Rounded2558
  | 6 => embedPair2542 batchC02701MinusMidpointP006Rounded2558
  | 7 => embedPair2542 batchC02701MinusMidpointP007Rounded2558
  | 8 => embedPair2542 batchC02701MinusMidpointP008Rounded2558
  | 9 => embedPair2542 batchC02701MinusMidpointP009Rounded2558
  | 10 => embedPair2542 batchC02701MinusMidpointP010Rounded2558
  | 11 => embedPair2542 batchC02701MinusMidpointP011Rounded2558
  | 12 => embedPair2542 batchC02701MinusMidpointP012Rounded2558
  | 13 => embedPair2542 batchC02701MinusMidpointP013Rounded2558
  | 14 => embedPair2542 batchC02701MinusMidpointP014Rounded2558
  | 15 => embedPair2542 batchC02701MinusMidpointP015Rounded2558
  | 16 => embedPair2542 batchC02701MinusMidpointP016Rounded2558
  | 17 => embedPair2542 batchC02701MinusMidpointP017Rounded2558
  | 18 => embedPair2542 batchC02701MinusMidpointP018Rounded2558
  | 19 => embedPair2542 batchC02701MinusMidpointP019Rounded2558
  | 20 => embedPair2542 batchC02701MinusMidpointP020Rounded2558
  | 21 => embedPair2542 batchC02701MinusMidpointP021Rounded2558
  | 22 => embedPair2542 batchC02701MinusMidpointP022Rounded2558
  | 23 => embedPair2542 batchC02701MinusMidpointP023Rounded2558
  | 24 => embedPair2542 batchC02701MinusMidpointP024Rounded2558
  | 25 => embedPair2542 batchC02701MinusMidpointP025Rounded2558
  | 26 => embedPair2542 batchC02701MinusMidpointP026Rounded2558
  | 27 => embedPair2542 batchC02701MinusMidpointP027Rounded2558
  | 28 => embedPair2542 batchC02701MinusMidpointP028Rounded2558
  | 29 => embedPair2542 batchC02701MinusMidpointP029Rounded2558
  | _ => 0

noncomputable def batchC02701MinusSignedMidpointError2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02701MinusMidpointP000Radius2558
  | 1 => batchC02701MinusMidpointP001Radius2558
  | 2 => batchC02701MinusMidpointP002Radius2558
  | 3 => batchC02701MinusMidpointP003Radius2558
  | 4 => batchC02701MinusMidpointP004Radius2558
  | 5 => batchC02701MinusMidpointP005Radius2558
  | 6 => batchC02701MinusMidpointP006Radius2558
  | 7 => batchC02701MinusMidpointP007Radius2558
  | 8 => batchC02701MinusMidpointP008Radius2558
  | 9 => batchC02701MinusMidpointP009Radius2558
  | 10 => batchC02701MinusMidpointP010Radius2558
  | 11 => batchC02701MinusMidpointP011Radius2558
  | 12 => batchC02701MinusMidpointP012Radius2558
  | 13 => batchC02701MinusMidpointP013Radius2558
  | 14 => batchC02701MinusMidpointP014Radius2558
  | 15 => batchC02701MinusMidpointP015Radius2558
  | 16 => batchC02701MinusMidpointP016Radius2558
  | 17 => batchC02701MinusMidpointP017Radius2558
  | 18 => batchC02701MinusMidpointP018Radius2558
  | 19 => batchC02701MinusMidpointP019Radius2558
  | 20 => batchC02701MinusMidpointP020Radius2558
  | 21 => batchC02701MinusMidpointP021Radius2558
  | 22 => batchC02701MinusMidpointP022Radius2558
  | 23 => batchC02701MinusMidpointP023Radius2558
  | 24 => batchC02701MinusMidpointP024Radius2558
  | 25 => batchC02701MinusMidpointP025Radius2558
  | 26 => batchC02701MinusMidpointP026Radius2558
  | 27 => batchC02701MinusMidpointP027Radius2558
  | 28 => batchC02701MinusMidpointP028Radius2558
  | 29 => batchC02701MinusMidpointP029Radius2558
  | _ => 0

theorem batchC02701MinusSignedMidpointExpError2558 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02701MinusMidpointPosition2558 -
        batchC02701MinusSignedMidpointValue2558 i‖ ≤ batchC02701MinusSignedMidpointError2558 i :=
            by
  fin_cases i
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP000RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP001RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP002RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP003RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP004RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP005RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP006RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP007RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP008RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP009RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP010RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP011RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP012RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP013RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP014RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP015RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP016RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP017RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP018RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP019RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP020RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP021RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP022RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP023RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP024RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP025RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP026RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP027RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP028RoundedError2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP029RoundedError2558

theorem batchC02701MinusSignedMidpointUnitNorm2558 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02701MinusMidpointPosition2558‖ ≤ 1
        := by
  fin_cases i
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP000DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP001DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP002DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP003DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP004DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP005DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP006DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP007DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP008DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP009DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP010DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP011DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP012DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP013DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP014DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP015DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP016DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP017DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP018DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP019DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP020DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP021DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP022DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP023DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP024DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP025DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP026DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP027DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP028DerivativeNorm2558
  · simpa only [batchC02701MinusSignedMidpointValue2558, batchC02701MinusSignedMidpointError2558]
      using
      batchC02701MinusMidpointP029DerivativeNorm2558

noncomputable def batchC02701MinusSignedMidpointSum2558 : ℂ := ⟨(((-(((162339 * 10^40
        + 600576782056458740796203337329098316304) * 10^40
        + 9431037281831219323913526076300116155797) * 10^40
        + 8013130612334575199942657563817761263525)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216)),
    (((-(((9761 * 10^40
        + 2240273921416695134703411762924158328651) * 10^40
        + 2248734868109615325267092549389026740899) * 10^40
        + 9497016933103973769910587096571505299915)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216))⟩

noncomputable def batchC02701MinusSignedMidpointUpper2558 : ℝ := ((187703 : ℝ) /
        50000000)

theorem batchC02701MinusSignedMidpointSum_eq2558 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02701MinusSignedMidpointValue2558 i) =
      batchC02701MinusSignedMidpointSum2558 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
        batchC02701MinusSignedMidpointValue2558,
      batchC02701MinusSignedMidpointSum2558, embedPair2542,
          batchC02701MinusMidpointP000Rounded2558,
      batchC02701MinusMidpointP001Rounded2558,
      batchC02701MinusMidpointP002Rounded2558,
      batchC02701MinusMidpointP003Rounded2558,
      batchC02701MinusMidpointP004Rounded2558,
      batchC02701MinusMidpointP005Rounded2558,
      batchC02701MinusMidpointP006Rounded2558,
      batchC02701MinusMidpointP007Rounded2558,
      batchC02701MinusMidpointP008Rounded2558,
      batchC02701MinusMidpointP009Rounded2558,
      batchC02701MinusMidpointP010Rounded2558,
      batchC02701MinusMidpointP011Rounded2558,
      batchC02701MinusMidpointP012Rounded2558,
      batchC02701MinusMidpointP013Rounded2558,
      batchC02701MinusMidpointP014Rounded2558,
      batchC02701MinusMidpointP015Rounded2558,
      batchC02701MinusMidpointP016Rounded2558,
      batchC02701MinusMidpointP017Rounded2558,
      batchC02701MinusMidpointP018Rounded2558,
      batchC02701MinusMidpointP019Rounded2558,
      batchC02701MinusMidpointP020Rounded2558,
      batchC02701MinusMidpointP021Rounded2558,
      batchC02701MinusMidpointP022Rounded2558,
      batchC02701MinusMidpointP023Rounded2558,
      batchC02701MinusMidpointP024Rounded2558,
      batchC02701MinusMidpointP025Rounded2558,
      batchC02701MinusMidpointP026Rounded2558,
      batchC02701MinusMidpointP027Rounded2558,
      batchC02701MinusMidpointP028Rounded2558,
      batchC02701MinusMidpointP029Rounded2558, Complex.mul_re, Complex.mul_im]

theorem batchC02701MinusSignedMidpointSum_norm2558 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02701MinusSignedMidpointValue2558 i‖ ≤
        ((93849 : ℝ) /
        25000000) := by
  rw [batchC02701MinusSignedMidpointSum_eq2558]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchC02701MinusSignedMidpointSum2558]

theorem batchC02701MinusSignedMidpointCharge2558 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchC02701MinusSignedMidpointError2558 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
      batchC02701MinusSignedMidpointError2558,
      batchC02701MinusMidpointP000Radius2558,
      batchC02701MinusMidpointP001Radius2558,
      batchC02701MinusMidpointP002Radius2558,
      batchC02701MinusMidpointP003Radius2558,
      batchC02701MinusMidpointP004Radius2558,
      batchC02701MinusMidpointP005Radius2558,
      batchC02701MinusMidpointP006Radius2558,
      batchC02701MinusMidpointP007Radius2558,
      batchC02701MinusMidpointP008Radius2558,
      batchC02701MinusMidpointP009Radius2558,
      batchC02701MinusMidpointP010Radius2558,
      batchC02701MinusMidpointP011Radius2558,
      batchC02701MinusMidpointP012Radius2558,
      batchC02701MinusMidpointP013Radius2558,
      batchC02701MinusMidpointP014Radius2558,
      batchC02701MinusMidpointP015Radius2558,
      batchC02701MinusMidpointP016Radius2558,
      batchC02701MinusMidpointP017Radius2558,
      batchC02701MinusMidpointP018Radius2558,
      batchC02701MinusMidpointP019Radius2558,
      batchC02701MinusMidpointP020Radius2558,
      batchC02701MinusMidpointP021Radius2558,
      batchC02701MinusMidpointP022Radius2558,
      batchC02701MinusMidpointP023Radius2558,
      batchC02701MinusMidpointP024Radius2558,
      batchC02701MinusMidpointP025Radius2558,
      batchC02701MinusMidpointP026Radius2558,
      batchC02701MinusMidpointP027Radius2558,
      batchC02701MinusMidpointP028Radius2558,
      batchC02701MinusMidpointP029Radius2558]

theorem batchC02701MinusSignedMidpointUpper_le2558 :
    signedJetUpper2539 2 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchC02701MinusMidpointPosition2558 ≤
          batchC02701MinusSignedMidpointUpper2558 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02701MinusMidpointPosition2558‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02701MinusSignedMidpointValue2558 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchC02701MinusSignedMidpointError2558 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (batchC02701MinusSignedMidpointExpError2558 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02701MinusMidpointPosition2558‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchC02701MinusSignedMidpointUnitNorm2558 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i batchC02701MinusMidpointPosition2558‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchC02701MinusSignedMidpointUpper2558
  linarith [batchC02701MinusSignedMidpointSum_norm2558, batchC02701MinusSignedMidpointCharge2558]

theorem batchC02701MinusPhysicalSecond2558 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        batchC02701MinusMidpointPosition2558‖ ≤
      batchC02701MinusSignedMidpointUpper2558 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchC02701MinusMidpointPosition2558
  exact h.trans batchC02701MinusSignedMidpointUpper_le2558

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02701MinusSignedMidpointExpError2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusSignedMidpointSum_eq2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusSignedMidpointCharge2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusSignedMidpointUpper_le2558
#print axioms ConnesWeilRH.Dev.batchC02701MinusPhysicalSecond2558
