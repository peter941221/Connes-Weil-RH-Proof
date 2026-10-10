import ConnesWeilRH.Dev.C1RouteABatchC02703PlusMidpoint2654

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem batchC02703PlusMidpoint_triangle2654 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def batchC02703PlusMidpointP000Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP000Radius2654 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02703PlusMidpointP000RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP000Factor2654
        batchC02703PlusMidpointP000Center2654) =
        batchC02703PlusMidpointP000Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP000RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP000Rounded2654‖ ≤
          batchC02703PlusMidpointP000Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP000Factor2654
      batchC02703PlusMidpointP000Center2654)
  rw [batchC02703PlusMidpointP000RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP000Factor2654 * embedPair2542
        batchC02703PlusMidpointP000Center2654)
    (embedPair2542 batchC02703PlusMidpointP000Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP000DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP000Factor2654,
      batchC02703PlusMidpointP000Error2654, rounding2542,
      batchC02703PlusMidpointP000Radius2654]

theorem batchC02703PlusMidpointP000DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP000Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP000RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP000Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP000Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP000Rounded2654]

def batchC02703PlusMidpointP001Rounded2654 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP001Radius2654 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP001RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP001Factor2654
        batchC02703PlusMidpointP001Center2654) =
        batchC02703PlusMidpointP001Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP001RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP001Rounded2654‖ ≤
          batchC02703PlusMidpointP001Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP001Factor2654
      batchC02703PlusMidpointP001Center2654)
  rw [batchC02703PlusMidpointP001RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP001Factor2654 * embedPair2542
        batchC02703PlusMidpointP001Center2654)
    (embedPair2542 batchC02703PlusMidpointP001Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP001DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP001Factor2654,
      batchC02703PlusMidpointP001Error2654, rounding2542,
      batchC02703PlusMidpointP001Radius2654]

theorem batchC02703PlusMidpointP001DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP001Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP001RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP001Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP001Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP001Rounded2654]

def batchC02703PlusMidpointP002Rounded2654 : RatPair2542 :=
  (((1737117 : ℚ) /
        1267650600228229401496703205376),
    (((-966041) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02703PlusMidpointP002Radius2654 : ℝ := ((2199023263407 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP002RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP002Factor2654
        batchC02703PlusMidpointP002Center2654) =
        batchC02703PlusMidpointP002Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP002RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP002Rounded2654‖ ≤
          batchC02703PlusMidpointP002Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP002Factor2654
      batchC02703PlusMidpointP002Center2654)
  rw [batchC02703PlusMidpointP002RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP002Factor2654 * embedPair2542
        batchC02703PlusMidpointP002Center2654)
    (embedPair2542 batchC02703PlusMidpointP002Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP002DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP002Factor2654,
      batchC02703PlusMidpointP002Error2654, rounding2542,
      batchC02703PlusMidpointP002Radius2654]

theorem batchC02703PlusMidpointP002DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP002Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP002RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP002Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP002Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP002Rounded2654]

def batchC02703PlusMidpointP003Rounded2654 : RatPair2542 :=
  (((15533280439767 : ℚ) /
        1267650600228229401496703205376),
    ((3232516280987 : ℚ) /
        633825300114114700748351602688))

noncomputable def batchC02703PlusMidpointP003Radius2654 : ℝ := ((2283131054207 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP003RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP003Factor2654
        batchC02703PlusMidpointP003Center2654) =
        batchC02703PlusMidpointP003Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP003RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP003Rounded2654‖ ≤
          batchC02703PlusMidpointP003Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP003Factor2654
      batchC02703PlusMidpointP003Center2654)
  rw [batchC02703PlusMidpointP003RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP003Factor2654 * embedPair2542
        batchC02703PlusMidpointP003Center2654)
    (embedPair2542 batchC02703PlusMidpointP003Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP003DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP003Factor2654,
      batchC02703PlusMidpointP003Error2654, rounding2542,
      batchC02703PlusMidpointP003Radius2654]

theorem batchC02703PlusMidpointP003DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP003Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP003RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP003Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP003Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP003Rounded2654]

def batchC02703PlusMidpointP004Rounded2654 : RatPair2542 :=
  (((2795912320504985 : ℚ) /
        633825300114114700748351602688),
    (((-4960526708129503) : ℚ) /
        1267650600228229401496703205376))

noncomputable def batchC02703PlusMidpointP004Radius2654 : ℝ := ((8963968845965 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02703PlusMidpointP004RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP004Factor2654
        batchC02703PlusMidpointP004Center2654) =
        batchC02703PlusMidpointP004Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP004RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP004Rounded2654‖ ≤
          batchC02703PlusMidpointP004Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP004Factor2654
      batchC02703PlusMidpointP004Center2654)
  rw [batchC02703PlusMidpointP004RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP004Factor2654 * embedPair2542
        batchC02703PlusMidpointP004Center2654)
    (embedPair2542 batchC02703PlusMidpointP004Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP004DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP004Factor2654,
      batchC02703PlusMidpointP004Error2654, rounding2542,
      batchC02703PlusMidpointP004Radius2654]

theorem batchC02703PlusMidpointP004DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP004Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP004RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP004Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP004Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP004Rounded2654]

def batchC02703PlusMidpointP005Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP005Radius2654 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem batchC02703PlusMidpointP005RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP005Factor2654
        batchC02703PlusMidpointP005Center2654) =
        batchC02703PlusMidpointP005Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP005RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP005Rounded2654‖ ≤
          batchC02703PlusMidpointP005Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP005Factor2654
      batchC02703PlusMidpointP005Center2654)
  rw [batchC02703PlusMidpointP005RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP005Factor2654 * embedPair2542
        batchC02703PlusMidpointP005Center2654)
    (embedPair2542 batchC02703PlusMidpointP005Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP005DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP005Factor2654,
      batchC02703PlusMidpointP005Error2654, rounding2542,
      batchC02703PlusMidpointP005Radius2654]

theorem batchC02703PlusMidpointP005DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP005Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP005RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP005Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP005Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP005Rounded2654]

def batchC02703PlusMidpointP006Rounded2654 : RatPair2542 :=
  (((5 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP006Radius2654 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP006RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP006Factor2654
        batchC02703PlusMidpointP006Center2654) =
        batchC02703PlusMidpointP006Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP006RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP006Rounded2654‖ ≤
          batchC02703PlusMidpointP006Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP006Factor2654
      batchC02703PlusMidpointP006Center2654)
  rw [batchC02703PlusMidpointP006RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP006Factor2654 * embedPair2542
        batchC02703PlusMidpointP006Center2654)
    (embedPair2542 batchC02703PlusMidpointP006Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP006DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP006Factor2654,
      batchC02703PlusMidpointP006Error2654, rounding2542,
      batchC02703PlusMidpointP006Radius2654]

theorem batchC02703PlusMidpointP006DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP006Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP006RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP006Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP006Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP006Rounded2654]

def batchC02703PlusMidpointP007Rounded2654 : RatPair2542 :=
  (((1946877485415 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP007Radius2654 : ℝ := ((2199305854301 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP007RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP007Factor2654
        batchC02703PlusMidpointP007Center2654) =
        batchC02703PlusMidpointP007Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP007RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP007Rounded2654‖ ≤
          batchC02703PlusMidpointP007Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP007Factor2654
      batchC02703PlusMidpointP007Center2654)
  rw [batchC02703PlusMidpointP007RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP007Factor2654 * embedPair2542
        batchC02703PlusMidpointP007Center2654)
    (embedPair2542 batchC02703PlusMidpointP007Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP007DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP007Factor2654,
      batchC02703PlusMidpointP007Error2654, rounding2542,
      batchC02703PlusMidpointP007Radius2654]

theorem batchC02703PlusMidpointP007DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP007Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP007RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP007Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP007Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP007Rounded2654]

def batchC02703PlusMidpointP008Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP008Radius2654 : ℝ := ((549758369123 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02703PlusMidpointP008RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP008Factor2654
        batchC02703PlusMidpointP008Center2654) =
        batchC02703PlusMidpointP008Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP008RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP008Rounded2654‖ ≤
          batchC02703PlusMidpointP008Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP008Factor2654
      batchC02703PlusMidpointP008Center2654)
  rw [batchC02703PlusMidpointP008RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP008Factor2654 * embedPair2542
        batchC02703PlusMidpointP008Center2654)
    (embedPair2542 batchC02703PlusMidpointP008Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP008DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP008Factor2654,
      batchC02703PlusMidpointP008Error2654, rounding2542,
      batchC02703PlusMidpointP008Radius2654]

theorem batchC02703PlusMidpointP008DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP008Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP008RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP008Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP008Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP008Rounded2654]

def batchC02703PlusMidpointP009Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP009Radius2654 : ℝ := ((274879184569 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02703PlusMidpointP009RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP009Factor2654
        batchC02703PlusMidpointP009Center2654) =
        batchC02703PlusMidpointP009Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP009RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP009Rounded2654‖ ≤
          batchC02703PlusMidpointP009Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP009Factor2654
      batchC02703PlusMidpointP009Center2654)
  rw [batchC02703PlusMidpointP009RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP009Factor2654 * embedPair2542
        batchC02703PlusMidpointP009Center2654)
    (embedPair2542 batchC02703PlusMidpointP009Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP009DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP009Factor2654,
      batchC02703PlusMidpointP009Error2654, rounding2542,
      batchC02703PlusMidpointP009Radius2654]

theorem batchC02703PlusMidpointP009DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP009Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP009RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP009Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP009Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP009Rounded2654]

def batchC02703PlusMidpointP010Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP010Radius2654 : ℝ := ((549758369147 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem batchC02703PlusMidpointP010RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP010Factor2654
        batchC02703PlusMidpointP010Center2654) =
        batchC02703PlusMidpointP010Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP010RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP010Rounded2654‖ ≤
          batchC02703PlusMidpointP010Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP010Factor2654
      batchC02703PlusMidpointP010Center2654)
  rw [batchC02703PlusMidpointP010RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP010Factor2654 * embedPair2542
        batchC02703PlusMidpointP010Center2654)
    (embedPair2542 batchC02703PlusMidpointP010Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP010DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP010Factor2654,
      batchC02703PlusMidpointP010Error2654, rounding2542,
      batchC02703PlusMidpointP010Radius2654]

theorem batchC02703PlusMidpointP010DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP010Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP010RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP010Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP010Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP010Rounded2654]

def batchC02703PlusMidpointP011Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP011Radius2654 : ℝ := ((2199033476611 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP011RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP011Factor2654
        batchC02703PlusMidpointP011Center2654) =
        batchC02703PlusMidpointP011Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP011RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP011Rounded2654‖ ≤
          batchC02703PlusMidpointP011Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP011Factor2654
      batchC02703PlusMidpointP011Center2654)
  rw [batchC02703PlusMidpointP011RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP011Factor2654 * embedPair2542
        batchC02703PlusMidpointP011Center2654)
    (embedPair2542 batchC02703PlusMidpointP011Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP011DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP011Factor2654,
      batchC02703PlusMidpointP011Error2654, rounding2542,
      batchC02703PlusMidpointP011Radius2654]

theorem batchC02703PlusMidpointP011DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP011Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP011RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP011Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP011Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP011Rounded2654]

def batchC02703PlusMidpointP012Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP012Radius2654 : ℝ := ((2199033476635 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP012RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP012Factor2654
        batchC02703PlusMidpointP012Center2654) =
        batchC02703PlusMidpointP012Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP012RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP012Rounded2654‖ ≤
          batchC02703PlusMidpointP012Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP012Factor2654
      batchC02703PlusMidpointP012Center2654)
  rw [batchC02703PlusMidpointP012RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP012Factor2654 * embedPair2542
        batchC02703PlusMidpointP012Center2654)
    (embedPair2542 batchC02703PlusMidpointP012Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP012DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP012Factor2654,
      batchC02703PlusMidpointP012Error2654, rounding2542,
      batchC02703PlusMidpointP012Radius2654]

theorem batchC02703PlusMidpointP012DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP012Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP012RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP012Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP012Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP012Rounded2654]

def batchC02703PlusMidpointP013Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP013Radius2654 : ℝ := ((1099516738329 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02703PlusMidpointP013RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP013Factor2654
        batchC02703PlusMidpointP013Center2654) =
        batchC02703PlusMidpointP013Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP013RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP013Rounded2654‖ ≤
          batchC02703PlusMidpointP013Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP013Factor2654
      batchC02703PlusMidpointP013Center2654)
  rw [batchC02703PlusMidpointP013RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP013Factor2654 * embedPair2542
        batchC02703PlusMidpointP013Center2654)
    (embedPair2542 batchC02703PlusMidpointP013Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP013DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP013Factor2654,
      batchC02703PlusMidpointP013Error2654, rounding2542,
      batchC02703PlusMidpointP013Radius2654]

theorem batchC02703PlusMidpointP013DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP013Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP013RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP013Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP013Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP013Rounded2654]

def batchC02703PlusMidpointP014Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP014Radius2654 : ℝ := ((2199033476699 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP014RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP014Factor2654
        batchC02703PlusMidpointP014Center2654) =
        batchC02703PlusMidpointP014Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP014RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP014Rounded2654‖ ≤
          batchC02703PlusMidpointP014Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP014Factor2654
      batchC02703PlusMidpointP014Center2654)
  rw [batchC02703PlusMidpointP014RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP014Factor2654 * embedPair2542
        batchC02703PlusMidpointP014Center2654)
    (embedPair2542 batchC02703PlusMidpointP014Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP014DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP014Factor2654,
      batchC02703PlusMidpointP014Error2654, rounding2542,
      batchC02703PlusMidpointP014Radius2654]

theorem batchC02703PlusMidpointP014DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP014Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP014RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP014Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP014Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP014Rounded2654]

def batchC02703PlusMidpointP015Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP015Radius2654 : ℝ := ((274879184591 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02703PlusMidpointP015RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP015Factor2654
        batchC02703PlusMidpointP015Center2654) =
        batchC02703PlusMidpointP015Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP015RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP015Rounded2654‖ ≤
          batchC02703PlusMidpointP015Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP015Factor2654
      batchC02703PlusMidpointP015Center2654)
  rw [batchC02703PlusMidpointP015RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP015Factor2654 * embedPair2542
        batchC02703PlusMidpointP015Center2654)
    (embedPair2542 batchC02703PlusMidpointP015Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP015DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP015Factor2654,
      batchC02703PlusMidpointP015Error2654, rounding2542,
      batchC02703PlusMidpointP015Radius2654]

theorem batchC02703PlusMidpointP015DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP015Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP015RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP015Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP015Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP015Rounded2654]

def batchC02703PlusMidpointP016Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP016Radius2654 : ℝ := ((2199033476749 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP016RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP016Factor2654
        batchC02703PlusMidpointP016Center2654) =
        batchC02703PlusMidpointP016Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP016RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP016Rounded2654‖ ≤
          batchC02703PlusMidpointP016Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP016Factor2654
      batchC02703PlusMidpointP016Center2654)
  rw [batchC02703PlusMidpointP016RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP016Factor2654 * embedPair2542
        batchC02703PlusMidpointP016Center2654)
    (embedPair2542 batchC02703PlusMidpointP016Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP016DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP016Factor2654,
      batchC02703PlusMidpointP016Error2654, rounding2542,
      batchC02703PlusMidpointP016Radius2654]

theorem batchC02703PlusMidpointP016DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP016Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP016RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP016Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP016Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP016Rounded2654]

def batchC02703PlusMidpointP017Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP017Radius2654 : ℝ := ((2199033476791 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP017RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP017Factor2654
        batchC02703PlusMidpointP017Center2654) =
        batchC02703PlusMidpointP017Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP017RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP017Rounded2654‖ ≤
          batchC02703PlusMidpointP017Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP017Factor2654
      batchC02703PlusMidpointP017Center2654)
  rw [batchC02703PlusMidpointP017RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP017Factor2654 * embedPair2542
        batchC02703PlusMidpointP017Center2654)
    (embedPair2542 batchC02703PlusMidpointP017Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP017DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP017Factor2654,
      batchC02703PlusMidpointP017Error2654, rounding2542,
      batchC02703PlusMidpointP017Radius2654]

theorem batchC02703PlusMidpointP017DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP017Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP017RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP017Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP017Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP017Rounded2654]

def batchC02703PlusMidpointP018Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP018Radius2654 : ℝ := ((1099516738403 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02703PlusMidpointP018RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP018Factor2654
        batchC02703PlusMidpointP018Center2654) =
        batchC02703PlusMidpointP018Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP018RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP018Rounded2654‖ ≤
          batchC02703PlusMidpointP018Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP018Factor2654
      batchC02703PlusMidpointP018Center2654)
  rw [batchC02703PlusMidpointP018RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP018Factor2654 * embedPair2542
        batchC02703PlusMidpointP018Center2654)
    (embedPair2542 batchC02703PlusMidpointP018Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP018DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP018Factor2654,
      batchC02703PlusMidpointP018Error2654, rounding2542,
      batchC02703PlusMidpointP018Radius2654]

theorem batchC02703PlusMidpointP018DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP018Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP018RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP018Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP018Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP018Rounded2654]

def batchC02703PlusMidpointP019Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP019Radius2654 : ℝ := ((2199033476835 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP019RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP019Factor2654
        batchC02703PlusMidpointP019Center2654) =
        batchC02703PlusMidpointP019Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP019RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP019Rounded2654‖ ≤
          batchC02703PlusMidpointP019Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP019Factor2654
      batchC02703PlusMidpointP019Center2654)
  rw [batchC02703PlusMidpointP019RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP019Factor2654 * embedPair2542
        batchC02703PlusMidpointP019Center2654)
    (embedPair2542 batchC02703PlusMidpointP019Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP019DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP019Factor2654,
      batchC02703PlusMidpointP019Error2654, rounding2542,
      batchC02703PlusMidpointP019Radius2654]

theorem batchC02703PlusMidpointP019DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP019Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP019RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP019Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP019Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP019Rounded2654]

def batchC02703PlusMidpointP020Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP020Radius2654 : ℝ := ((2199033476865 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP020RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP020Factor2654
        batchC02703PlusMidpointP020Center2654) =
        batchC02703PlusMidpointP020Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP020RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP020Rounded2654‖ ≤
          batchC02703PlusMidpointP020Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP020Factor2654
      batchC02703PlusMidpointP020Center2654)
  rw [batchC02703PlusMidpointP020RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP020Factor2654 * embedPair2542
        batchC02703PlusMidpointP020Center2654)
    (embedPair2542 batchC02703PlusMidpointP020Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP020DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP020Factor2654,
      batchC02703PlusMidpointP020Error2654, rounding2542,
      batchC02703PlusMidpointP020Radius2654]

theorem batchC02703PlusMidpointP020DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP020Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP020RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP020Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP020Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP020Rounded2654]

def batchC02703PlusMidpointP021Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP021Radius2654 : ℝ := ((2199033476891 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP021RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP021Factor2654
        batchC02703PlusMidpointP021Center2654) =
        batchC02703PlusMidpointP021Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP021RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP021Rounded2654‖ ≤
          batchC02703PlusMidpointP021Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP021Factor2654
      batchC02703PlusMidpointP021Center2654)
  rw [batchC02703PlusMidpointP021RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP021Factor2654 * embedPair2542
        batchC02703PlusMidpointP021Center2654)
    (embedPair2542 batchC02703PlusMidpointP021Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP021DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP021Factor2654,
      batchC02703PlusMidpointP021Error2654, rounding2542,
      batchC02703PlusMidpointP021Radius2654]

theorem batchC02703PlusMidpointP021DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP021Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP021RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP021Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP021Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP021Rounded2654]

def batchC02703PlusMidpointP022Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP022Radius2654 : ℝ := ((274879184613 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02703PlusMidpointP022RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP022Factor2654
        batchC02703PlusMidpointP022Center2654) =
        batchC02703PlusMidpointP022Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP022RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP022Rounded2654‖ ≤
          batchC02703PlusMidpointP022Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP022Factor2654
      batchC02703PlusMidpointP022Center2654)
  rw [batchC02703PlusMidpointP022RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP022Factor2654 * embedPair2542
        batchC02703PlusMidpointP022Center2654)
    (embedPair2542 batchC02703PlusMidpointP022Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP022DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP022Factor2654,
      batchC02703PlusMidpointP022Error2654, rounding2542,
      batchC02703PlusMidpointP022Radius2654]

theorem batchC02703PlusMidpointP022DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP022Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP022RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP022Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP022Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP022Rounded2654]

def batchC02703PlusMidpointP023Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP023Radius2654 : ℝ := ((1099516738471 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem batchC02703PlusMidpointP023RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP023Factor2654
        batchC02703PlusMidpointP023Center2654) =
        batchC02703PlusMidpointP023Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP023RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP023Rounded2654‖ ≤
          batchC02703PlusMidpointP023Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP023Factor2654
      batchC02703PlusMidpointP023Center2654)
  rw [batchC02703PlusMidpointP023RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP023Factor2654 * embedPair2542
        batchC02703PlusMidpointP023Center2654)
    (embedPair2542 batchC02703PlusMidpointP023Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP023DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP023Factor2654,
      batchC02703PlusMidpointP023Error2654, rounding2542,
      batchC02703PlusMidpointP023Radius2654]

theorem batchC02703PlusMidpointP023DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP023Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP023RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP023Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP023Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP023Rounded2654]

def batchC02703PlusMidpointP024Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP024Radius2654 : ℝ := ((2199033476959 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP024RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP024Factor2654
        batchC02703PlusMidpointP024Center2654) =
        batchC02703PlusMidpointP024Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP024RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP024Rounded2654‖ ≤
          batchC02703PlusMidpointP024Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP024Factor2654
      batchC02703PlusMidpointP024Center2654)
  rw [batchC02703PlusMidpointP024RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP024Factor2654 * embedPair2542
        batchC02703PlusMidpointP024Center2654)
    (embedPair2542 batchC02703PlusMidpointP024Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP024DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP024Factor2654,
      batchC02703PlusMidpointP024Error2654, rounding2542,
      batchC02703PlusMidpointP024Radius2654]

theorem batchC02703PlusMidpointP024DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP024Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP024RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP024Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP024Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP024Rounded2654]

def batchC02703PlusMidpointP025Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP025Radius2654 : ℝ := ((2199033476981 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP025RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP025Factor2654
        batchC02703PlusMidpointP025Center2654) =
        batchC02703PlusMidpointP025Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP025RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP025Rounded2654‖ ≤
          batchC02703PlusMidpointP025Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP025Factor2654
      batchC02703PlusMidpointP025Center2654)
  rw [batchC02703PlusMidpointP025RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP025Factor2654 * embedPair2542
        batchC02703PlusMidpointP025Center2654)
    (embedPair2542 batchC02703PlusMidpointP025Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP025DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP025Factor2654,
      batchC02703PlusMidpointP025Error2654, rounding2542,
      batchC02703PlusMidpointP025Radius2654]

theorem batchC02703PlusMidpointP025DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP025Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP025RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP025Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP025Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP025Rounded2654]

def batchC02703PlusMidpointP026Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP026Radius2654 : ℝ := ((2199033477003 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP026RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP026Factor2654
        batchC02703PlusMidpointP026Center2654) =
        batchC02703PlusMidpointP026Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP026RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP026Rounded2654‖ ≤
          batchC02703PlusMidpointP026Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP026Factor2654
      batchC02703PlusMidpointP026Center2654)
  rw [batchC02703PlusMidpointP026RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP026Factor2654 * embedPair2542
        batchC02703PlusMidpointP026Center2654)
    (embedPair2542 batchC02703PlusMidpointP026Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP026DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP026Factor2654,
      batchC02703PlusMidpointP026Error2654, rounding2542,
      batchC02703PlusMidpointP026Radius2654]

theorem batchC02703PlusMidpointP026DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP026Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP026RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP026Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP026Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP026Rounded2654]

def batchC02703PlusMidpointP027Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP027Radius2654 : ℝ := ((2199033477035 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP027RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP027Factor2654
        batchC02703PlusMidpointP027Center2654) =
        batchC02703PlusMidpointP027Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP027RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP027Rounded2654‖ ≤
          batchC02703PlusMidpointP027Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP027Factor2654
      batchC02703PlusMidpointP027Center2654)
  rw [batchC02703PlusMidpointP027RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP027Factor2654 * embedPair2542
        batchC02703PlusMidpointP027Center2654)
    (embedPair2542 batchC02703PlusMidpointP027Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP027DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP027Factor2654,
      batchC02703PlusMidpointP027Error2654, rounding2542,
      batchC02703PlusMidpointP027Radius2654]

theorem batchC02703PlusMidpointP027DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP027Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP027RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP027Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP027Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP027Rounded2654]

def batchC02703PlusMidpointP028Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP028Radius2654 : ℝ := ((274879184631 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem batchC02703PlusMidpointP028RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP028Factor2654
        batchC02703PlusMidpointP028Center2654) =
        batchC02703PlusMidpointP028Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP028RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP028Rounded2654‖ ≤
          batchC02703PlusMidpointP028Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP028Factor2654
      batchC02703PlusMidpointP028Center2654)
  rw [batchC02703PlusMidpointP028RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP028Factor2654 * embedPair2542
        batchC02703PlusMidpointP028Center2654)
    (embedPair2542 batchC02703PlusMidpointP028Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP028DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP028Factor2654,
      batchC02703PlusMidpointP028Error2654, rounding2542,
      batchC02703PlusMidpointP028Radius2654]

theorem batchC02703PlusMidpointP028DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP028Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP028RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP028Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP028Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP028Rounded2654]

def batchC02703PlusMidpointP029Rounded2654 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703PlusMidpointP029Radius2654 : ℝ := ((2199033477067 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem batchC02703PlusMidpointP029RoundCompute2654 :
    pairRound2542 (pairMul2542 batchC02703PlusMidpointP029Factor2654
        batchC02703PlusMidpointP029Center2654) =
        batchC02703PlusMidpointP029Rounded2654 := by
  cbv

theorem batchC02703PlusMidpointP029RoundedError2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02703PlusMidpointPosition2654 -
      embedPair2542 batchC02703PlusMidpointP029Rounded2654‖ ≤
          batchC02703PlusMidpointP029Radius2654 := by
  have hr := embedPair_round_error2542 (pairMul2542 batchC02703PlusMidpointP029Factor2654
      batchC02703PlusMidpointP029Center2654)
  rw [batchC02703PlusMidpointP029RoundCompute2654, embedPair_mul2542] at hr
  have h := (batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP029Factor2654 * embedPair2542
        batchC02703PlusMidpointP029Center2654)
    (embedPair2542 batchC02703PlusMidpointP029Rounded2654)).trans (add_le_add
        batchC02703PlusMidpointP029DerivativeError2654 hr)
  apply h.trans
  norm_num [pairMagnitude2542, batchC02703PlusMidpointP029Factor2654,
      batchC02703PlusMidpointP029Error2654, rounding2542,
      batchC02703PlusMidpointP029Radius2654]

theorem batchC02703PlusMidpointP029DerivativeNorm2654 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02703PlusMidpointPosition2654‖ ≤ 1 := by
  have h := batchC02703PlusMidpoint_triangle2654
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02703PlusMidpointPosition2654)
    (embedPair2542 batchC02703PlusMidpointP029Rounded2654) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add batchC02703PlusMidpointP029RoundedError2654
      (embedPair_magnitude2542
      batchC02703PlusMidpointP029Rounded2654))
  apply h'.trans
  norm_num [batchC02703PlusMidpointP029Radius2654, pairMagnitude2542,
      batchC02703PlusMidpointP029Rounded2654]

noncomputable def batchC02703PlusSignedMidpointValue2654 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchC02703PlusMidpointP000Rounded2654
  | 1 => embedPair2542 batchC02703PlusMidpointP001Rounded2654
  | 2 => embedPair2542 batchC02703PlusMidpointP002Rounded2654
  | 3 => embedPair2542 batchC02703PlusMidpointP003Rounded2654
  | 4 => embedPair2542 batchC02703PlusMidpointP004Rounded2654
  | 5 => embedPair2542 batchC02703PlusMidpointP005Rounded2654
  | 6 => embedPair2542 batchC02703PlusMidpointP006Rounded2654
  | 7 => embedPair2542 batchC02703PlusMidpointP007Rounded2654
  | 8 => embedPair2542 batchC02703PlusMidpointP008Rounded2654
  | 9 => embedPair2542 batchC02703PlusMidpointP009Rounded2654
  | 10 => embedPair2542 batchC02703PlusMidpointP010Rounded2654
  | 11 => embedPair2542 batchC02703PlusMidpointP011Rounded2654
  | 12 => embedPair2542 batchC02703PlusMidpointP012Rounded2654
  | 13 => embedPair2542 batchC02703PlusMidpointP013Rounded2654
  | 14 => embedPair2542 batchC02703PlusMidpointP014Rounded2654
  | 15 => embedPair2542 batchC02703PlusMidpointP015Rounded2654
  | 16 => embedPair2542 batchC02703PlusMidpointP016Rounded2654
  | 17 => embedPair2542 batchC02703PlusMidpointP017Rounded2654
  | 18 => embedPair2542 batchC02703PlusMidpointP018Rounded2654
  | 19 => embedPair2542 batchC02703PlusMidpointP019Rounded2654
  | 20 => embedPair2542 batchC02703PlusMidpointP020Rounded2654
  | 21 => embedPair2542 batchC02703PlusMidpointP021Rounded2654
  | 22 => embedPair2542 batchC02703PlusMidpointP022Rounded2654
  | 23 => embedPair2542 batchC02703PlusMidpointP023Rounded2654
  | 24 => embedPair2542 batchC02703PlusMidpointP024Rounded2654
  | 25 => embedPair2542 batchC02703PlusMidpointP025Rounded2654
  | 26 => embedPair2542 batchC02703PlusMidpointP026Rounded2654
  | 27 => embedPair2542 batchC02703PlusMidpointP027Rounded2654
  | 28 => embedPair2542 batchC02703PlusMidpointP028Rounded2654
  | 29 => embedPair2542 batchC02703PlusMidpointP029Rounded2654
  | _ => 0

noncomputable def batchC02703PlusSignedMidpointError2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => batchC02703PlusMidpointP000Radius2654
  | 1 => batchC02703PlusMidpointP001Radius2654
  | 2 => batchC02703PlusMidpointP002Radius2654
  | 3 => batchC02703PlusMidpointP003Radius2654
  | 4 => batchC02703PlusMidpointP004Radius2654
  | 5 => batchC02703PlusMidpointP005Radius2654
  | 6 => batchC02703PlusMidpointP006Radius2654
  | 7 => batchC02703PlusMidpointP007Radius2654
  | 8 => batchC02703PlusMidpointP008Radius2654
  | 9 => batchC02703PlusMidpointP009Radius2654
  | 10 => batchC02703PlusMidpointP010Radius2654
  | 11 => batchC02703PlusMidpointP011Radius2654
  | 12 => batchC02703PlusMidpointP012Radius2654
  | 13 => batchC02703PlusMidpointP013Radius2654
  | 14 => batchC02703PlusMidpointP014Radius2654
  | 15 => batchC02703PlusMidpointP015Radius2654
  | 16 => batchC02703PlusMidpointP016Radius2654
  | 17 => batchC02703PlusMidpointP017Radius2654
  | 18 => batchC02703PlusMidpointP018Radius2654
  | 19 => batchC02703PlusMidpointP019Radius2654
  | 20 => batchC02703PlusMidpointP020Radius2654
  | 21 => batchC02703PlusMidpointP021Radius2654
  | 22 => batchC02703PlusMidpointP022Radius2654
  | 23 => batchC02703PlusMidpointP023Radius2654
  | 24 => batchC02703PlusMidpointP024Radius2654
  | 25 => batchC02703PlusMidpointP025Radius2654
  | 26 => batchC02703PlusMidpointP026Radius2654
  | 27 => batchC02703PlusMidpointP027Radius2654
  | 28 => batchC02703PlusMidpointP028Radius2654
  | 29 => batchC02703PlusMidpointP029Radius2654
  | _ => 0

theorem batchC02703PlusSignedMidpointExpError2654 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02703PlusMidpointPosition2654 -
        batchC02703PlusSignedMidpointValue2654 i‖ ≤ batchC02703PlusSignedMidpointError2654 i := by
  fin_cases i
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP000RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP001RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP002RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP003RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP004RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP005RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP006RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP007RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP008RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP009RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP010RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP011RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP012RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP013RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP014RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP015RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP016RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP017RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP018RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP019RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP020RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP021RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP022RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP023RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP024RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP025RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP026RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP027RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP028RoundedError2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP029RoundedError2654

theorem batchC02703PlusSignedMidpointUnitNorm2654 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02703PlusMidpointPosition2654‖ ≤ 1 :=
        by
  fin_cases i
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP000DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP001DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP002DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP003DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP004DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP005DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP006DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP007DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP008DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP009DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP010DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP011DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP012DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP013DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP014DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP015DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP016DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP017DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP018DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP019DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP020DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP021DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP022DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP023DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP024DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP025DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP026DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP027DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP028DerivativeNorm2654
  · simpa only [batchC02703PlusSignedMidpointValue2654, batchC02703PlusSignedMidpointError2654]
      using
      batchC02703PlusMidpointP029DerivativeNorm2654

noncomputable def batchC02703PlusSignedMidpointSum2654 : ℂ := ⟨(((-(((7470 * 10^40
        + 9829358631845698194968117594914853701614) * 10^40
        + 6838653104203018693557846803671743398816) * 10^40
        + 6526833738695401110922708105403310403157)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216)),
    (((-(((715 * 10^40
        + 569571880361139214815260944640209940696) * 10^40
        + 5893342295948897066763077693952187370478) * 10^40
        + 4568448069917736464200207164347722683965)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216))⟩

noncomputable def batchC02703PlusSignedMidpointUpper2654 : ℝ := ((8667 : ℝ) /
        50000000)

theorem batchC02703PlusSignedMidpointSum_eq2654 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02703PlusSignedMidpointValue2654 i) =
      batchC02703PlusSignedMidpointSum2654 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
        batchC02703PlusSignedMidpointValue2654,
      batchC02703PlusSignedMidpointSum2654, embedPair2542, batchC02703PlusMidpointP000Rounded2654,
      batchC02703PlusMidpointP001Rounded2654,
      batchC02703PlusMidpointP002Rounded2654,
      batchC02703PlusMidpointP003Rounded2654,
      batchC02703PlusMidpointP004Rounded2654,
      batchC02703PlusMidpointP005Rounded2654,
      batchC02703PlusMidpointP006Rounded2654,
      batchC02703PlusMidpointP007Rounded2654,
      batchC02703PlusMidpointP008Rounded2654,
      batchC02703PlusMidpointP009Rounded2654,
      batchC02703PlusMidpointP010Rounded2654,
      batchC02703PlusMidpointP011Rounded2654,
      batchC02703PlusMidpointP012Rounded2654,
      batchC02703PlusMidpointP013Rounded2654,
      batchC02703PlusMidpointP014Rounded2654,
      batchC02703PlusMidpointP015Rounded2654,
      batchC02703PlusMidpointP016Rounded2654,
      batchC02703PlusMidpointP017Rounded2654,
      batchC02703PlusMidpointP018Rounded2654,
      batchC02703PlusMidpointP019Rounded2654,
      batchC02703PlusMidpointP020Rounded2654,
      batchC02703PlusMidpointP021Rounded2654,
      batchC02703PlusMidpointP022Rounded2654,
      batchC02703PlusMidpointP023Rounded2654,
      batchC02703PlusMidpointP024Rounded2654,
      batchC02703PlusMidpointP025Rounded2654,
      batchC02703PlusMidpointP026Rounded2654,
      batchC02703PlusMidpointP027Rounded2654,
      batchC02703PlusMidpointP028Rounded2654,
      batchC02703PlusMidpointP029Rounded2654, Complex.mul_re, Complex.mul_im]

theorem batchC02703PlusSignedMidpointSum_norm2654 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02703PlusSignedMidpointValue2654 i‖ ≤
        ((4331 : ℝ) /
        25000000) := by
  rw [batchC02703PlusSignedMidpointSum_eq2654]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchC02703PlusSignedMidpointSum2654]

theorem batchC02703PlusSignedMidpointCharge2654 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchC02703PlusSignedMidpointError2654 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540,
      batchC02703PlusSignedMidpointError2654,
      batchC02703PlusMidpointP000Radius2654,
      batchC02703PlusMidpointP001Radius2654,
      batchC02703PlusMidpointP002Radius2654,
      batchC02703PlusMidpointP003Radius2654,
      batchC02703PlusMidpointP004Radius2654,
      batchC02703PlusMidpointP005Radius2654,
      batchC02703PlusMidpointP006Radius2654,
      batchC02703PlusMidpointP007Radius2654,
      batchC02703PlusMidpointP008Radius2654,
      batchC02703PlusMidpointP009Radius2654,
      batchC02703PlusMidpointP010Radius2654,
      batchC02703PlusMidpointP011Radius2654,
      batchC02703PlusMidpointP012Radius2654,
      batchC02703PlusMidpointP013Radius2654,
      batchC02703PlusMidpointP014Radius2654,
      batchC02703PlusMidpointP015Radius2654,
      batchC02703PlusMidpointP016Radius2654,
      batchC02703PlusMidpointP017Radius2654,
      batchC02703PlusMidpointP018Radius2654,
      batchC02703PlusMidpointP019Radius2654,
      batchC02703PlusMidpointP020Radius2654,
      batchC02703PlusMidpointP021Radius2654,
      batchC02703PlusMidpointP022Radius2654,
      batchC02703PlusMidpointP023Radius2654,
      batchC02703PlusMidpointP024Radius2654,
      batchC02703PlusMidpointP025Radius2654,
      batchC02703PlusMidpointP026Radius2654,
      batchC02703PlusMidpointP027Radius2654,
      batchC02703PlusMidpointP028Radius2654,
      batchC02703PlusMidpointP029Radius2654]

theorem batchC02703PlusSignedMidpointUpper_le2654 :
    signedJetUpper2539 2 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchC02703PlusMidpointPosition2654 ≤
          batchC02703PlusSignedMidpointUpper2654 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02703PlusMidpointPosition2654‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchC02703PlusSignedMidpointValue2654 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchC02703PlusSignedMidpointError2654 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (batchC02703PlusSignedMidpointExpError2654 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02703PlusMidpointPosition2654‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchC02703PlusSignedMidpointUnitNorm2654 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i batchC02703PlusMidpointPosition2654‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchC02703PlusSignedMidpointUpper2654
  linarith [batchC02703PlusSignedMidpointSum_norm2654, batchC02703PlusSignedMidpointCharge2654]

theorem batchC02703PlusPhysicalSecond2654 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        batchC02703PlusMidpointPosition2654‖ ≤
      batchC02703PlusSignedMidpointUpper2654 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchC02703PlusMidpointPosition2654
  exact h.trans batchC02703PlusSignedMidpointUpper_le2654

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02703PlusSignedMidpointExpError2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusSignedMidpointSum_eq2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusSignedMidpointCharge2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusSignedMidpointUpper_le2654
#print axioms ConnesWeilRH.Dev.batchC02703PlusPhysicalSecond2654
