import ConnesWeilRH.Dev.C1RouteABatchC02704PlusMidpoint2654

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem batchC02704PlusMidpoint_triangle2654 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def batchC02704PlusMidpointP000Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP000Radius2654 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02704PlusMidpointP000RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP000Factor2654
        batchC02704PlusMidpointP000Center2654) =
        batchC02704PlusMidpointP000Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP000RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP000Rounded2654‖ ≤
          batchC02704PlusMidpointP000Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP000Factor2654
      batchC02704PlusMidpointP000Center2654)
  rw [batchC02704PlusMidpointP000RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP000Factor2654 * embedPair2542
        batchC02704PlusMidpointP000Center2654)
    (embedPair2542 batchC02704PlusMidpointP000Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP000DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP000Factor2654,
      batchC02704PlusMidpointP000Error2654, rounding2542,
      batchC02704PlusMidpointP000Radius2654]

theorem batchC02704PlusMidpointP000DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP000Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP000RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP000Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP000Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP000Rounded2654]

def batchC02704PlusMidpointP001Rounded2654 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP001Radius2654 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704PlusMidpointP001RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP001Factor2654
        batchC02704PlusMidpointP001Center2654) =
        batchC02704PlusMidpointP001Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP001RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP001Rounded2654‖ ≤
          batchC02704PlusMidpointP001Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP001Factor2654
      batchC02704PlusMidpointP001Center2654)
  rw [batchC02704PlusMidpointP001RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP001Factor2654 * embedPair2542
        batchC02704PlusMidpointP001Center2654)
    (embedPair2542 batchC02704PlusMidpointP001Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP001DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP001Factor2654,
      batchC02704PlusMidpointP001Error2654, rounding2542,
      batchC02704PlusMidpointP001Radius2654]

theorem batchC02704PlusMidpointP001DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP001Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP001RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP001Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP001Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP001Rounded2654]

def batchC02704PlusMidpointP002Rounded2654 : RatPair2542 :=
  (((939791 : ℚ) /
        633825300114114700748351602688),
    (((-919997) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02704PlusMidpointP002Radius2654 : ℝ := ((2199023263843 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704PlusMidpointP002RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP002Factor2654
        batchC02704PlusMidpointP002Center2654) =
        batchC02704PlusMidpointP002Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP002RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP002Rounded2654‖ ≤
          batchC02704PlusMidpointP002Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP002Factor2654
      batchC02704PlusMidpointP002Center2654)
  rw [batchC02704PlusMidpointP002RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP002Factor2654 * embedPair2542
        batchC02704PlusMidpointP002Center2654)
    (embedPair2542 batchC02704PlusMidpointP002Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP002DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP002Factor2654,
      batchC02704PlusMidpointP002Error2654, rounding2542,
      batchC02704PlusMidpointP002Radius2654]

theorem batchC02704PlusMidpointP002DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP002Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP002RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP002Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP002Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP002Rounded2654]

def batchC02704PlusMidpointP003Rounded2654 : RatPair2542 :=
  (((15468612549831 : ℚ) /
        1267650600228229401496703205376),
    ((7384872992835 : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02704PlusMidpointP003Radius2654 : ℝ := ((2285104108861 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704PlusMidpointP003RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP003Factor2654
        batchC02704PlusMidpointP003Center2654) =
        batchC02704PlusMidpointP003Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP003RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP003Rounded2654‖ ≤
          batchC02704PlusMidpointP003Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP003Factor2654
      batchC02704PlusMidpointP003Center2654)
  rw [batchC02704PlusMidpointP003RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP003Factor2654 * embedPair2542
        batchC02704PlusMidpointP003Center2654)
    (embedPair2542 batchC02704PlusMidpointP003Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP003DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP003Factor2654,
      batchC02704PlusMidpointP003Error2654, rounding2542,
      batchC02704PlusMidpointP003Radius2654]

theorem batchC02704PlusMidpointP003DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP003Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP003RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP003Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP003Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP003Rounded2654]

def batchC02704PlusMidpointP004Rounded2654 : RatPair2542 :=
  (((5386163419844231 : ℚ) /
        1267650600228229401496703205376),
    (((-1321986241225235) : ℚ) /
        316912650057057350374175801344))

noncomputable def batchC02704PlusMidpointP004Radius2654 : ℝ := ((18169707125695 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02704PlusMidpointP004RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP004Factor2654
        batchC02704PlusMidpointP004Center2654) =
        batchC02704PlusMidpointP004Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP004RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP004Rounded2654‖ ≤
          batchC02704PlusMidpointP004Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP004Factor2654
      batchC02704PlusMidpointP004Center2654)
  rw [batchC02704PlusMidpointP004RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP004Factor2654 * embedPair2542
        batchC02704PlusMidpointP004Center2654)
    (embedPair2542 batchC02704PlusMidpointP004Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP004DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP004Factor2654,
      batchC02704PlusMidpointP004Error2654, rounding2542,
      batchC02704PlusMidpointP004Radius2654]

theorem batchC02704PlusMidpointP004DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP004Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP004RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP004Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP004Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP004Rounded2654]

def batchC02704PlusMidpointP005Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP005Radius2654 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02704PlusMidpointP005RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP005Factor2654
        batchC02704PlusMidpointP005Center2654) =
        batchC02704PlusMidpointP005Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP005RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP005Rounded2654‖ ≤
          batchC02704PlusMidpointP005Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP005Factor2654
      batchC02704PlusMidpointP005Center2654)
  rw [batchC02704PlusMidpointP005RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP005Factor2654 * embedPair2542
        batchC02704PlusMidpointP005Center2654)
    (embedPair2542 batchC02704PlusMidpointP005Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP005DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP005Factor2654,
      batchC02704PlusMidpointP005Error2654, rounding2542,
      batchC02704PlusMidpointP005Radius2654]

theorem batchC02704PlusMidpointP005DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP005Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP005RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP005Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP005Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP005Rounded2654]

def batchC02704PlusMidpointP006Rounded2654 : RatPair2542 :=
  (((5 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP006Radius2654 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704PlusMidpointP006RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP006Factor2654
        batchC02704PlusMidpointP006Center2654) =
        batchC02704PlusMidpointP006Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP006RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP006Rounded2654‖ ≤
          batchC02704PlusMidpointP006Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP006Factor2654
      batchC02704PlusMidpointP006Center2654)
  rw [batchC02704PlusMidpointP006RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP006Factor2654 * embedPair2542
        batchC02704PlusMidpointP006Center2654)
    (embedPair2542 batchC02704PlusMidpointP006Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP006DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP006Factor2654,
      batchC02704PlusMidpointP006Error2654, rounding2542,
      batchC02704PlusMidpointP006Radius2654]

theorem batchC02704PlusMidpointP006DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP006Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP006RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP006Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP006Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP006Rounded2654]

def batchC02704PlusMidpointP007Rounded2654 : RatPair2542 :=
  (((61851051757 : ℚ) /
        39614081257132168796771975168),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP007Radius2654 : ℝ := ((274913808261 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02704PlusMidpointP007RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP007Factor2654
        batchC02704PlusMidpointP007Center2654) =
        batchC02704PlusMidpointP007Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP007RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP007Rounded2654‖ ≤
          batchC02704PlusMidpointP007Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP007Factor2654
      batchC02704PlusMidpointP007Center2654)
  rw [batchC02704PlusMidpointP007RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP007Factor2654 * embedPair2542
        batchC02704PlusMidpointP007Center2654)
    (embedPair2542 batchC02704PlusMidpointP007Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP007DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP007Factor2654,
      batchC02704PlusMidpointP007Error2654, rounding2542,
      batchC02704PlusMidpointP007Radius2654]

theorem batchC02704PlusMidpointP007DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP007Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP007RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP007Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP007Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP007Rounded2654]

def batchC02704PlusMidpointP008Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP008Radius2654 : ℝ := ((2199026995695 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704PlusMidpointP008RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP008Factor2654
        batchC02704PlusMidpointP008Center2654) =
        batchC02704PlusMidpointP008Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP008RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP008Rounded2654‖ ≤
          batchC02704PlusMidpointP008Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP008Factor2654
      batchC02704PlusMidpointP008Center2654)
  rw [batchC02704PlusMidpointP008RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP008Factor2654 * embedPair2542
        batchC02704PlusMidpointP008Center2654)
    (embedPair2542 batchC02704PlusMidpointP008Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP008DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP008Factor2654,
      batchC02704PlusMidpointP008Error2654, rounding2542,
      batchC02704PlusMidpointP008Radius2654]

theorem batchC02704PlusMidpointP008DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP008Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP008RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP008Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP008Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP008Rounded2654]

def batchC02704PlusMidpointP009Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP009Radius2654 : ℝ := ((549756748933 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02704PlusMidpointP009RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP009Factor2654
        batchC02704PlusMidpointP009Center2654) =
        batchC02704PlusMidpointP009Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP009RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP009Rounded2654‖ ≤
          batchC02704PlusMidpointP009Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP009Factor2654
      batchC02704PlusMidpointP009Center2654)
  rw [batchC02704PlusMidpointP009RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP009Factor2654 * embedPair2542
        batchC02704PlusMidpointP009Center2654)
    (embedPair2542 batchC02704PlusMidpointP009Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP009DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP009Factor2654,
      batchC02704PlusMidpointP009Error2654, rounding2542,
      batchC02704PlusMidpointP009Radius2654]

theorem batchC02704PlusMidpointP009DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP009Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP009RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP009Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP009Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP009Rounded2654]

def batchC02704PlusMidpointP010Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP010Radius2654 : ℝ := ((1099513497877 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02704PlusMidpointP010RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP010Factor2654
        batchC02704PlusMidpointP010Center2654) =
        batchC02704PlusMidpointP010Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP010RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP010Rounded2654‖ ≤
          batchC02704PlusMidpointP010Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP010Factor2654
      batchC02704PlusMidpointP010Center2654)
  rw [batchC02704PlusMidpointP010RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP010Factor2654 * embedPair2542
        batchC02704PlusMidpointP010Center2654)
    (embedPair2542 batchC02704PlusMidpointP010Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP010DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP010Factor2654,
      batchC02704PlusMidpointP010Error2654, rounding2542,
      batchC02704PlusMidpointP010Radius2654]

theorem batchC02704PlusMidpointP010DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP010Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP010RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP010Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP010Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP010Rounded2654]

def batchC02704PlusMidpointP011Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP011Radius2654 : ℝ := ((274878374471 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02704PlusMidpointP011RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP011Factor2654
        batchC02704PlusMidpointP011Center2654) =
        batchC02704PlusMidpointP011Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP011RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP011Rounded2654‖ ≤
          batchC02704PlusMidpointP011Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP011Factor2654
      batchC02704PlusMidpointP011Center2654)
  rw [batchC02704PlusMidpointP011RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP011Factor2654 * embedPair2542
        batchC02704PlusMidpointP011Center2654)
    (embedPair2542 batchC02704PlusMidpointP011Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP011DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP011Factor2654,
      batchC02704PlusMidpointP011Error2654, rounding2542,
      batchC02704PlusMidpointP011Radius2654]

theorem batchC02704PlusMidpointP011DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP011Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP011RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP011Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP011Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP011Rounded2654]

def batchC02704PlusMidpointP012Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP012Radius2654 : ℝ := ((2199026995783 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704PlusMidpointP012RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP012Factor2654
        batchC02704PlusMidpointP012Center2654) =
        batchC02704PlusMidpointP012Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP012RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP012Rounded2654‖ ≤
          batchC02704PlusMidpointP012Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP012Factor2654
      batchC02704PlusMidpointP012Center2654)
  rw [batchC02704PlusMidpointP012RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP012Factor2654 * embedPair2542
        batchC02704PlusMidpointP012Center2654)
    (embedPair2542 batchC02704PlusMidpointP012Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP012DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP012Factor2654,
      batchC02704PlusMidpointP012Error2654, rounding2542,
      batchC02704PlusMidpointP012Radius2654]

theorem batchC02704PlusMidpointP012DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP012Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP012RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP012Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP012Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP012Rounded2654]

def batchC02704PlusMidpointP013Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP013Radius2654 : ℝ := ((549756748949 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02704PlusMidpointP013RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP013Factor2654
        batchC02704PlusMidpointP013Center2654) =
        batchC02704PlusMidpointP013Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP013RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP013Rounded2654‖ ≤
          batchC02704PlusMidpointP013Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP013Factor2654
      batchC02704PlusMidpointP013Center2654)
  rw [batchC02704PlusMidpointP013RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP013Factor2654 * embedPair2542
        batchC02704PlusMidpointP013Center2654)
    (embedPair2542 batchC02704PlusMidpointP013Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP013DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP013Factor2654,
      batchC02704PlusMidpointP013Error2654, rounding2542,
      batchC02704PlusMidpointP013Radius2654]

theorem batchC02704PlusMidpointP013DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP013Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP013RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP013Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP013Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP013Rounded2654]

def batchC02704PlusMidpointP014Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP014Radius2654 : ℝ := ((2199026995821 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704PlusMidpointP014RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP014Factor2654
        batchC02704PlusMidpointP014Center2654) =
        batchC02704PlusMidpointP014Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP014RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP014Rounded2654‖ ≤
          batchC02704PlusMidpointP014Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP014Factor2654
      batchC02704PlusMidpointP014Center2654)
  rw [batchC02704PlusMidpointP014RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP014Factor2654 * embedPair2542
        batchC02704PlusMidpointP014Center2654)
    (embedPair2542 batchC02704PlusMidpointP014Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP014DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP014Factor2654,
      batchC02704PlusMidpointP014Error2654, rounding2542,
      batchC02704PlusMidpointP014Radius2654]

theorem batchC02704PlusMidpointP014DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP014Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP014RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP014Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP014Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP014Rounded2654]

def batchC02704PlusMidpointP015Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP015Radius2654 : ℝ := ((2199026995839 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704PlusMidpointP015RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP015Factor2654
        batchC02704PlusMidpointP015Center2654) =
        batchC02704PlusMidpointP015Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP015RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP015Rounded2654‖ ≤
          batchC02704PlusMidpointP015Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP015Factor2654
      batchC02704PlusMidpointP015Center2654)
  rw [batchC02704PlusMidpointP015RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP015Factor2654 * embedPair2542
        batchC02704PlusMidpointP015Center2654)
    (embedPair2542 batchC02704PlusMidpointP015Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP015DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP015Factor2654,
      batchC02704PlusMidpointP015Error2654, rounding2542,
      batchC02704PlusMidpointP015Radius2654]

theorem batchC02704PlusMidpointP015DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP015Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP015RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP015Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP015Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP015Rounded2654]

def batchC02704PlusMidpointP016Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP016Radius2654 : ℝ := ((2199026995851 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704PlusMidpointP016RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP016Factor2654
        batchC02704PlusMidpointP016Center2654) =
        batchC02704PlusMidpointP016Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP016RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP016Rounded2654‖ ≤
          batchC02704PlusMidpointP016Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP016Factor2654
      batchC02704PlusMidpointP016Center2654)
  rw [batchC02704PlusMidpointP016RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP016Factor2654 * embedPair2542
        batchC02704PlusMidpointP016Center2654)
    (embedPair2542 batchC02704PlusMidpointP016Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP016DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP016Factor2654,
      batchC02704PlusMidpointP016Error2654, rounding2542,
      batchC02704PlusMidpointP016Radius2654]

theorem batchC02704PlusMidpointP016DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP016Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP016RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP016Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP016Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP016Rounded2654]

def batchC02704PlusMidpointP017Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP017Radius2654 : ℝ := ((549756748969 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02704PlusMidpointP017RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP017Factor2654
        batchC02704PlusMidpointP017Center2654) =
        batchC02704PlusMidpointP017Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP017RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP017Rounded2654‖ ≤
          batchC02704PlusMidpointP017Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP017Factor2654
      batchC02704PlusMidpointP017Center2654)
  rw [batchC02704PlusMidpointP017RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP017Factor2654 * embedPair2542
        batchC02704PlusMidpointP017Center2654)
    (embedPair2542 batchC02704PlusMidpointP017Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP017DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP017Factor2654,
      batchC02704PlusMidpointP017Error2654, rounding2542,
      batchC02704PlusMidpointP017Radius2654]

theorem batchC02704PlusMidpointP017DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP017Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP017RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP017Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP017Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP017Rounded2654]

def batchC02704PlusMidpointP018Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP018Radius2654 : ℝ := ((1099513497943 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02704PlusMidpointP018RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP018Factor2654
        batchC02704PlusMidpointP018Center2654) =
        batchC02704PlusMidpointP018Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP018RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP018Rounded2654‖ ≤
          batchC02704PlusMidpointP018Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP018Factor2654
      batchC02704PlusMidpointP018Center2654)
  rw [batchC02704PlusMidpointP018RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP018Factor2654 * embedPair2542
        batchC02704PlusMidpointP018Center2654)
    (embedPair2542 batchC02704PlusMidpointP018Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP018DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP018Factor2654,
      batchC02704PlusMidpointP018Error2654, rounding2542,
      batchC02704PlusMidpointP018Radius2654]

theorem batchC02704PlusMidpointP018DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP018Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP018RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP018Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP018Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP018Rounded2654]

def batchC02704PlusMidpointP019Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP019Radius2654 : ℝ := ((2199026995903 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704PlusMidpointP019RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP019Factor2654
        batchC02704PlusMidpointP019Center2654) =
        batchC02704PlusMidpointP019Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP019RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP019Rounded2654‖ ≤
          batchC02704PlusMidpointP019Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP019Factor2654
      batchC02704PlusMidpointP019Center2654)
  rw [batchC02704PlusMidpointP019RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP019Factor2654 * embedPair2542
        batchC02704PlusMidpointP019Center2654)
    (embedPair2542 batchC02704PlusMidpointP019Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP019DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP019Factor2654,
      batchC02704PlusMidpointP019Error2654, rounding2542,
      batchC02704PlusMidpointP019Radius2654]

theorem batchC02704PlusMidpointP019DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP019Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP019RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP019Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP019Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP019Rounded2654]

def batchC02704PlusMidpointP020Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP020Radius2654 : ℝ := ((1099513497961 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02704PlusMidpointP020RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP020Factor2654
        batchC02704PlusMidpointP020Center2654) =
        batchC02704PlusMidpointP020Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP020RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP020Rounded2654‖ ≤
          batchC02704PlusMidpointP020Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP020Factor2654
      batchC02704PlusMidpointP020Center2654)
  rw [batchC02704PlusMidpointP020RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP020Factor2654 * embedPair2542
        batchC02704PlusMidpointP020Center2654)
    (embedPair2542 batchC02704PlusMidpointP020Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP020DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP020Factor2654,
      batchC02704PlusMidpointP020Error2654, rounding2542,
      batchC02704PlusMidpointP020Radius2654]

theorem batchC02704PlusMidpointP020DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP020Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP020RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP020Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP020Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP020Rounded2654]

def batchC02704PlusMidpointP021Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP021Radius2654 : ℝ := ((2199026995937 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704PlusMidpointP021RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP021Factor2654
        batchC02704PlusMidpointP021Center2654) =
        batchC02704PlusMidpointP021Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP021RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP021Rounded2654‖ ≤
          batchC02704PlusMidpointP021Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP021Factor2654
      batchC02704PlusMidpointP021Center2654)
  rw [batchC02704PlusMidpointP021RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP021Factor2654 * embedPair2542
        batchC02704PlusMidpointP021Center2654)
    (embedPair2542 batchC02704PlusMidpointP021Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP021DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP021Factor2654,
      batchC02704PlusMidpointP021Error2654, rounding2542,
      batchC02704PlusMidpointP021Radius2654]

theorem batchC02704PlusMidpointP021DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP021Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP021RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP021Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP021Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP021Rounded2654]

def batchC02704PlusMidpointP022Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP022Radius2654 : ℝ := ((2199026995945 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704PlusMidpointP022RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP022Factor2654
        batchC02704PlusMidpointP022Center2654) =
        batchC02704PlusMidpointP022Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP022RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP022Rounded2654‖ ≤
          batchC02704PlusMidpointP022Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP022Factor2654
      batchC02704PlusMidpointP022Center2654)
  rw [batchC02704PlusMidpointP022RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP022Factor2654 * embedPair2542
        batchC02704PlusMidpointP022Center2654)
    (embedPair2542 batchC02704PlusMidpointP022Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP022DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP022Factor2654,
      batchC02704PlusMidpointP022Error2654, rounding2542,
      batchC02704PlusMidpointP022Radius2654]

theorem batchC02704PlusMidpointP022DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP022Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP022RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP022Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP022Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP022Rounded2654]

def batchC02704PlusMidpointP023Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP023Radius2654 : ℝ := ((8589949203 : ℝ) /
        5444517870735015415413993718908291383296)

theorem batchC02704PlusMidpointP023RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP023Factor2654
        batchC02704PlusMidpointP023Center2654) =
        batchC02704PlusMidpointP023Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP023RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP023Rounded2654‖ ≤
          batchC02704PlusMidpointP023Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP023Factor2654
      batchC02704PlusMidpointP023Center2654)
  rw [batchC02704PlusMidpointP023RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP023Factor2654 * embedPair2542
        batchC02704PlusMidpointP023Center2654)
    (embedPair2542 batchC02704PlusMidpointP023Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP023DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP023Factor2654,
      batchC02704PlusMidpointP023Error2654, rounding2542,
      batchC02704PlusMidpointP023Radius2654]

theorem batchC02704PlusMidpointP023DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP023Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP023RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP023Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP023Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP023Rounded2654]

def batchC02704PlusMidpointP024Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP024Radius2654 : ℝ := ((1099513497989 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02704PlusMidpointP024RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP024Factor2654
        batchC02704PlusMidpointP024Center2654) =
        batchC02704PlusMidpointP024Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP024RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP024Rounded2654‖ ≤
          batchC02704PlusMidpointP024Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP024Factor2654
      batchC02704PlusMidpointP024Center2654)
  rw [batchC02704PlusMidpointP024RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP024Factor2654 * embedPair2542
        batchC02704PlusMidpointP024Center2654)
    (embedPair2542 batchC02704PlusMidpointP024Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP024DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP024Factor2654,
      batchC02704PlusMidpointP024Error2654, rounding2542,
      batchC02704PlusMidpointP024Radius2654]

theorem batchC02704PlusMidpointP024DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP024Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP024RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP024Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP024Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP024Rounded2654]

def batchC02704PlusMidpointP025Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP025Radius2654 : ℝ := ((2199026995991 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704PlusMidpointP025RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP025Factor2654
        batchC02704PlusMidpointP025Center2654) =
        batchC02704PlusMidpointP025Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP025RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP025Rounded2654‖ ≤
          batchC02704PlusMidpointP025Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP025Factor2654
      batchC02704PlusMidpointP025Center2654)
  rw [batchC02704PlusMidpointP025RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP025Factor2654 * embedPair2542
        batchC02704PlusMidpointP025Center2654)
    (embedPair2542 batchC02704PlusMidpointP025Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP025DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP025Factor2654,
      batchC02704PlusMidpointP025Error2654, rounding2542,
      batchC02704PlusMidpointP025Radius2654]

theorem batchC02704PlusMidpointP025DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP025Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP025RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP025Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP025Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP025Rounded2654]

def batchC02704PlusMidpointP026Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP026Radius2654 : ℝ := ((2199026996005 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02704PlusMidpointP026RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP026Factor2654
        batchC02704PlusMidpointP026Center2654) =
        batchC02704PlusMidpointP026Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP026RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP026Rounded2654‖ ≤
          batchC02704PlusMidpointP026Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP026Factor2654
      batchC02704PlusMidpointP026Center2654)
  rw [batchC02704PlusMidpointP026RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP026Factor2654 * embedPair2542
        batchC02704PlusMidpointP026Center2654)
    (embedPair2542 batchC02704PlusMidpointP026Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP026DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP026Factor2654,
      batchC02704PlusMidpointP026Error2654, rounding2542,
      batchC02704PlusMidpointP026Radius2654]

theorem batchC02704PlusMidpointP026DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP026Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP026RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP026Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP026Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP026Rounded2654]

def batchC02704PlusMidpointP027Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP027Radius2654 : ℝ := ((274878374503 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02704PlusMidpointP027RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP027Factor2654
        batchC02704PlusMidpointP027Center2654) =
        batchC02704PlusMidpointP027Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP027RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP027Rounded2654‖ ≤
          batchC02704PlusMidpointP027Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP027Factor2654
      batchC02704PlusMidpointP027Center2654)
  rw [batchC02704PlusMidpointP027RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP027Factor2654 * embedPair2542
        batchC02704PlusMidpointP027Center2654)
    (embedPair2542 batchC02704PlusMidpointP027Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP027DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP027Factor2654,
      batchC02704PlusMidpointP027Error2654, rounding2542,
      batchC02704PlusMidpointP027Radius2654]

theorem batchC02704PlusMidpointP027DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP027Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP027RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP027Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP027Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP027Rounded2654]

def batchC02704PlusMidpointP028Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP028Radius2654 : ℝ := ((34359796813 : ℝ) /
        (2 * 10^40
        + 1778071482940061661655974875633165533184))

theorem batchC02704PlusMidpointP028RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP028Factor2654
        batchC02704PlusMidpointP028Center2654) =
        batchC02704PlusMidpointP028Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP028RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP028Rounded2654‖ ≤
          batchC02704PlusMidpointP028Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP028Factor2654
      batchC02704PlusMidpointP028Center2654)
  rw [batchC02704PlusMidpointP028RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP028Factor2654 * embedPair2542
        batchC02704PlusMidpointP028Center2654)
    (embedPair2542 batchC02704PlusMidpointP028Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP028DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP028Factor2654,
      batchC02704PlusMidpointP028Error2654, rounding2542,
      batchC02704PlusMidpointP028Radius2654]

theorem batchC02704PlusMidpointP028DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP028Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP028RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP028Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP028Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP028Rounded2654]

def batchC02704PlusMidpointP029Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02704PlusMidpointP029Radius2654 : ℝ := ((549756749011 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02704PlusMidpointP029RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02704PlusMidpointP029Factor2654
        batchC02704PlusMidpointP029Center2654) =
        batchC02704PlusMidpointP029Rounded2654 := by
  cbv

theorem batchC02704PlusMidpointP029RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02704PlusMidpointPosition2654 -
      embedPair2542 batchC02704PlusMidpointP029Rounded2654‖ ≤
          batchC02704PlusMidpointP029Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02704PlusMidpointP029Factor2654
      batchC02704PlusMidpointP029Center2654)
  rw [batchC02704PlusMidpointP029RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP029Factor2654 * embedPair2542
        batchC02704PlusMidpointP029Center2654)
    (embedPair2542 batchC02704PlusMidpointP029Rounded2654)).trans (add_le_add
        batchC02704PlusMidpointP029DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02704PlusMidpointP029Factor2654,
      batchC02704PlusMidpointP029Error2654, rounding2542,
      batchC02704PlusMidpointP029Radius2654]

theorem batchC02704PlusMidpointP029DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02704PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02704PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02704PlusMidpointPosition2654)
    (embedPair2542 batchC02704PlusMidpointP029Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02704PlusMidpointP029RoundedError2654
      (embedPair_magnitude2542
      batchC02704PlusMidpointP029Rounded2654))
  apply h'.trans
  norm_num [batchC02704PlusMidpointP029Radius2654, pairMagnitude2542,
      batchC02704PlusMidpointP029Rounded2654]

noncomputable def batchC02704PlusSignedMidpointValue2654 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchC02704PlusMidpointP000Rounded2654
  | 1 => embedPair2542 batchC02704PlusMidpointP001Rounded2654
  | 2 => embedPair2542 batchC02704PlusMidpointP002Rounded2654
  | 3 => embedPair2542 batchC02704PlusMidpointP003Rounded2654
  | 4 => embedPair2542 batchC02704PlusMidpointP004Rounded2654
  | 5 => embedPair2542 batchC02704PlusMidpointP005Rounded2654
  | 6 => embedPair2542 batchC02704PlusMidpointP006Rounded2654
  | 7 => embedPair2542 batchC02704PlusMidpointP007Rounded2654
  | 8 => embedPair2542 batchC02704PlusMidpointP008Rounded2654
  | 9 => embedPair2542 batchC02704PlusMidpointP009Rounded2654
  | 10 => embedPair2542 batchC02704PlusMidpointP010Rounded2654
  | 11 => embedPair2542 batchC02704PlusMidpointP011Rounded2654
  | 12 => embedPair2542 batchC02704PlusMidpointP012Rounded2654
  | 13 => embedPair2542 batchC02704PlusMidpointP013Rounded2654
  | 14 => embedPair2542 batchC02704PlusMidpointP014Rounded2654
  | 15 => embedPair2542 batchC02704PlusMidpointP015Rounded2654
  | 16 => embedPair2542 batchC02704PlusMidpointP016Rounded2654
  | 17 => embedPair2542 batchC02704PlusMidpointP017Rounded2654
  | 18 => embedPair2542 batchC02704PlusMidpointP018Rounded2654
  | 19 => embedPair2542 batchC02704PlusMidpointP019Rounded2654
  | 20 => embedPair2542 batchC02704PlusMidpointP020Rounded2654
  | 21 => embedPair2542 batchC02704PlusMidpointP021Rounded2654
  | 22 => embedPair2542 batchC02704PlusMidpointP022Rounded2654
  | 23 => embedPair2542 batchC02704PlusMidpointP023Rounded2654
  | 24 => embedPair2542 batchC02704PlusMidpointP024Rounded2654
  | 25 => embedPair2542 batchC02704PlusMidpointP025Rounded2654
  | 26 => embedPair2542 batchC02704PlusMidpointP026Rounded2654
  | 27 => embedPair2542 batchC02704PlusMidpointP027Rounded2654
  | 28 => embedPair2542 batchC02704PlusMidpointP028Rounded2654
  | 29 => embedPair2542 batchC02704PlusMidpointP029Rounded2654
  | _ => 0

noncomputable def batchC02704PlusSignedMidpointError2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02704PlusMidpointP000Radius2654
  | 1 => batchC02704PlusMidpointP001Radius2654
  | 2 => batchC02704PlusMidpointP002Radius2654
  | 3 => batchC02704PlusMidpointP003Radius2654
  | 4 => batchC02704PlusMidpointP004Radius2654
  | 5 => batchC02704PlusMidpointP005Radius2654
  | 6 => batchC02704PlusMidpointP006Radius2654
  | 7 => batchC02704PlusMidpointP007Radius2654
  | 8 => batchC02704PlusMidpointP008Radius2654
  | 9 => batchC02704PlusMidpointP009Radius2654
  | 10 => batchC02704PlusMidpointP010Radius2654
  | 11 => batchC02704PlusMidpointP011Radius2654
  | 12 => batchC02704PlusMidpointP012Radius2654
  | 13 => batchC02704PlusMidpointP013Radius2654
  | 14 => batchC02704PlusMidpointP014Radius2654
  | 15 => batchC02704PlusMidpointP015Radius2654
  | 16 => batchC02704PlusMidpointP016Radius2654
  | 17 => batchC02704PlusMidpointP017Radius2654
  | 18 => batchC02704PlusMidpointP018Radius2654
  | 19 => batchC02704PlusMidpointP019Radius2654
  | 20 => batchC02704PlusMidpointP020Radius2654
  | 21 => batchC02704PlusMidpointP021Radius2654
  | 22 => batchC02704PlusMidpointP022Radius2654
  | 23 => batchC02704PlusMidpointP023Radius2654
  | 24 => batchC02704PlusMidpointP024Radius2654
  | 25 => batchC02704PlusMidpointP025Radius2654
  | 26 => batchC02704PlusMidpointP026Radius2654
  | 27 => batchC02704PlusMidpointP027Radius2654
  | 28 => batchC02704PlusMidpointP028Radius2654
  | 29 => batchC02704PlusMidpointP029Radius2654
  | _ => 0

theorem batchC02704PlusSignedMidpointExpError2654 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02704PlusMidpointPosition2654 -
        batchC02704PlusSignedMidpointValue2654 i‖ ≤ batchC02704PlusSignedMidpointError2654 i := by
  fin_cases i
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP000RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP001RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP002RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP003RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP004RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP005RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP006RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP007RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP008RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP009RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP010RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP011RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP012RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP013RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP014RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP015RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP016RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP017RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP018RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP019RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP020RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP021RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP022RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP023RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP024RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP025RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP026RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP027RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP028RoundedError2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP029RoundedError2654

theorem batchC02704PlusSignedMidpointUnitNorm2654 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02704PlusMidpointPosition2654‖ ≤ 1 :=
        by
  fin_cases i
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP000DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP001DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP002DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP003DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP004DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP005DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP006DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP007DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP008DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP009DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP010DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP011DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP012DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP013DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP014DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP015DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP016DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP017DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP018DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP019DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP020DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP021DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP022DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP023DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP024DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP025DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP026DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP027DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP028DerivativeNorm2654
  · simpa only [batchC02704PlusSignedMidpointValue2654, batchC02704PlusSignedMidpointError2654]
      using
      batchC02704PlusMidpointP029DerivativeNorm2654

noncomputable def batchC02704PlusSignedMidpointSum2654 : ℂ := ⟨(((-(((7381 * 10^40
        + 4645095842940053191322397581904457892751) * 10^40
        + 6764761374560468381925313656772735594048) * 10^40
        + 2226093707087636739374800080904955940021)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216)),
    (((-(((462 * 10^40
        + 2251284413848138549661055378863331606336) * 10^40
        + 7360206781423631219751986392040807200213) * 10^40
        + 2742046954237570621738734372703558661305)) : ℝ) /
        (((21661481 * 10^40
        + 9853188660904563608136178414330971646513) * 10^40
        + 7356699351937172355172896723145017999980) * 10^40
        + 47688590453885868835635965404913860608))⟩

noncomputable def batchC02704PlusSignedMidpointUpper2654 : ℝ := ((8591 : ℝ) /
        50000000)

theorem batchC02704PlusSignedMidpointSum_eq2654 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02704PlusSignedMidpointValue2654 i) =
      batchC02704PlusSignedMidpointSum2654 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
        batchC02704PlusSignedMidpointValue2654,
      batchC02704PlusSignedMidpointSum2654, embedPair2542, batchC02704PlusMidpointP000Rounded2654,
      batchC02704PlusMidpointP001Rounded2654,
      batchC02704PlusMidpointP002Rounded2654,
      batchC02704PlusMidpointP003Rounded2654,
      batchC02704PlusMidpointP004Rounded2654,
      batchC02704PlusMidpointP005Rounded2654,
      batchC02704PlusMidpointP006Rounded2654,
      batchC02704PlusMidpointP007Rounded2654,
      batchC02704PlusMidpointP008Rounded2654,
      batchC02704PlusMidpointP009Rounded2654,
      batchC02704PlusMidpointP010Rounded2654,
      batchC02704PlusMidpointP011Rounded2654,
      batchC02704PlusMidpointP012Rounded2654,
      batchC02704PlusMidpointP013Rounded2654,
      batchC02704PlusMidpointP014Rounded2654,
      batchC02704PlusMidpointP015Rounded2654,
      batchC02704PlusMidpointP016Rounded2654,
      batchC02704PlusMidpointP017Rounded2654,
      batchC02704PlusMidpointP018Rounded2654,
      batchC02704PlusMidpointP019Rounded2654,
      batchC02704PlusMidpointP020Rounded2654,
      batchC02704PlusMidpointP021Rounded2654,
      batchC02704PlusMidpointP022Rounded2654,
      batchC02704PlusMidpointP023Rounded2654,
      batchC02704PlusMidpointP024Rounded2654,
      batchC02704PlusMidpointP025Rounded2654,
      batchC02704PlusMidpointP026Rounded2654,
      batchC02704PlusMidpointP027Rounded2654,
      batchC02704PlusMidpointP028Rounded2654,
      batchC02704PlusMidpointP029Rounded2654, Complex.mul_re, Complex.mul_im]

theorem batchC02704PlusSignedMidpointSum_norm2654 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02704PlusSignedMidpointValue2654 i‖ ≤
        ((4293 : ℝ) /
        25000000) := by
  rw [batchC02704PlusSignedMidpointSum_eq2654]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchC02704PlusSignedMidpointSum2654]

theorem batchC02704PlusSignedMidpointCharge2654 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchC02704PlusSignedMidpointError2654 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
      batchC02704PlusSignedMidpointError2654,
      batchC02704PlusMidpointP000Radius2654,
      batchC02704PlusMidpointP001Radius2654,
      batchC02704PlusMidpointP002Radius2654,
      batchC02704PlusMidpointP003Radius2654,
      batchC02704PlusMidpointP004Radius2654,
      batchC02704PlusMidpointP005Radius2654,
      batchC02704PlusMidpointP006Radius2654,
      batchC02704PlusMidpointP007Radius2654,
      batchC02704PlusMidpointP008Radius2654,
      batchC02704PlusMidpointP009Radius2654,
      batchC02704PlusMidpointP010Radius2654,
      batchC02704PlusMidpointP011Radius2654,
      batchC02704PlusMidpointP012Radius2654,
      batchC02704PlusMidpointP013Radius2654,
      batchC02704PlusMidpointP014Radius2654,
      batchC02704PlusMidpointP015Radius2654,
      batchC02704PlusMidpointP016Radius2654,
      batchC02704PlusMidpointP017Radius2654,
      batchC02704PlusMidpointP018Radius2654,
      batchC02704PlusMidpointP019Radius2654,
      batchC02704PlusMidpointP020Radius2654,
      batchC02704PlusMidpointP021Radius2654,
      batchC02704PlusMidpointP022Radius2654,
      batchC02704PlusMidpointP023Radius2654,
      batchC02704PlusMidpointP024Radius2654,
      batchC02704PlusMidpointP025Radius2654,
      batchC02704PlusMidpointP026Radius2654,
      batchC02704PlusMidpointP027Radius2654,
      batchC02704PlusMidpointP028Radius2654,
      batchC02704PlusMidpointP029Radius2654]

theorem batchC02704PlusSignedMidpointUpper_le2654 :
    signedJetUpper2539 2 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchC02704PlusMidpointPosition2654 ≤
          batchC02704PlusSignedMidpointUpper2654 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02704PlusMidpointPosition2654‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02704PlusSignedMidpointValue2654 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchC02704PlusSignedMidpointError2654 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (batchC02704PlusSignedMidpointExpError2654 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02704PlusMidpointPosition2654‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchC02704PlusSignedMidpointUnitNorm2654 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02704PlusMidpointPosition2654‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchC02704PlusSignedMidpointUpper2654
  linarith [batchC02704PlusSignedMidpointSum_norm2654, batchC02704PlusSignedMidpointCharge2654]

theorem batchC02704PlusPhysicalSecond2654 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        batchC02704PlusMidpointPosition2654‖ ≤
      batchC02704PlusSignedMidpointUpper2654 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchC02704PlusMidpointPosition2654
  exact h.trans batchC02704PlusSignedMidpointUpper_le2654

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02704PlusSignedMidpointExpError2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusSignedMidpointSum_eq2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusSignedMidpointCharge2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusSignedMidpointUpper_le2654
#print axioms ConnesWeilRH.Dev.batchC02704PlusPhysicalSecond2654
