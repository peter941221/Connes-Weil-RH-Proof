import ConnesWeilRH.Dev.C1RouteABoundaryMidpoint2548

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem edgeMidpoint_triangle2549 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def edgeMidpointP000Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP000Radius2549 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem edgeMidpointP000RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP000Factor2548 edgeMidpointP000Center2548) =
        edgeMidpointP000Rounded2549 := by
  cbv

theorem edgeMidpointP000RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP000Rounded2549‖ ≤ edgeMidpointP000Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP000Factor2548
      edgeMidpointP000Center2548)
  rw [edgeMidpointP000RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP000Factor2548 * embedPair2542 edgeMidpointP000Center2548)
    (embedPair2542 edgeMidpointP000Rounded2549)).trans (add_le_add
        edgeMidpointP000DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP000Factor2548, edgeMidpointP000Error2548,
      rounding2542,
      edgeMidpointP000Radius2549]

theorem edgeMidpointP000DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩ edgeMidpointPosition2548‖ ≤ 1 :=
        by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP000Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP000RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP000Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP000Radius2549, pairMagnitude2542, edgeMidpointP000Rounded2549]

def edgeMidpointP001Rounded2549 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP001Radius2549 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem edgeMidpointP001RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP001Factor2548 edgeMidpointP001Center2548) =
        edgeMidpointP001Rounded2549 := by
  cbv

theorem edgeMidpointP001RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP001Rounded2549‖ ≤ edgeMidpointP001Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP001Factor2548
      edgeMidpointP001Center2548)
  rw [edgeMidpointP001RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP001Factor2548 * embedPair2542 edgeMidpointP001Center2548)
    (embedPair2542 edgeMidpointP001Rounded2549)).trans (add_le_add
        edgeMidpointP001DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP001Factor2548, edgeMidpointP001Error2548,
      rounding2542,
      edgeMidpointP001Radius2549]

theorem edgeMidpointP001DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩ edgeMidpointPosition2548‖ ≤ 1 :=
        by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP001Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP001RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP001Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP001Radius2549, pairMagnitude2542, edgeMidpointP001Rounded2549]

def edgeMidpointP002Rounded2549 : RatPair2542 :=
  (((1339907 : ℚ) /
        1267650600228229401496703205376),
    (((-524869) : ℚ) /
        633825300114114700748351602688))

noncomputable def edgeMidpointP002Radius2549 : ℝ := ((2199023262191 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem edgeMidpointP002RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP002Factor2548 edgeMidpointP002Center2548) =
        edgeMidpointP002Rounded2549 := by
  cbv

theorem edgeMidpointP002RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP002Rounded2549‖ ≤ edgeMidpointP002Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP002Factor2548
      edgeMidpointP002Center2548)
  rw [edgeMidpointP002RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP002Factor2548 * embedPair2542 edgeMidpointP002Center2548)
    (embedPair2542 edgeMidpointP002Rounded2549)).trans (add_le_add
        edgeMidpointP002DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP002Factor2548, edgeMidpointP002Error2548,
      rounding2542,
      edgeMidpointP002Radius2549]

theorem edgeMidpointP002DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩ edgeMidpointPosition2548‖ ≤ 1 :=
        by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP002Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP002RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP002Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP002Radius2549, pairMagnitude2542, edgeMidpointP002Rounded2549]

def edgeMidpointP003Rounded2549 : RatPair2542 :=
  (((15448181489715 : ℚ) /
        1267650600228229401496703205376),
    ((3802480427995 : ℚ) /
        1267650600228229401496703205376))

noncomputable def edgeMidpointP003Radius2549 : ℝ := ((569261515263 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem edgeMidpointP003RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP003Factor2548 edgeMidpointP003Center2548) =
        edgeMidpointP003Rounded2549 := by
  cbv

theorem edgeMidpointP003RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP003Rounded2549‖ ≤ edgeMidpointP003Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP003Factor2548
      edgeMidpointP003Center2548)
  rw [edgeMidpointP003RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP003Factor2548 * embedPair2542 edgeMidpointP003Center2548)
    (embedPair2542 edgeMidpointP003Rounded2549)).trans (add_le_add
        edgeMidpointP003DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP003Factor2548, edgeMidpointP003Error2548,
      rounding2542,
      edgeMidpointP003Radius2549]

theorem edgeMidpointP003DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩ edgeMidpointPosition2548‖ ≤ 1 :=
        by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP003Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP003RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP003Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP003Radius2549, pairMagnitude2542, edgeMidpointP003Rounded2549]

def edgeMidpointP004Rounded2549 : RatPair2542 :=
  (((762028936138355 : ℚ) /
        158456325028528675187087900672),
    (((-1970922237903599) : ℚ) /
        633825300114114700748351602688))

noncomputable def edgeMidpointP004Radius2549 : ℝ := ((17135354181433 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem edgeMidpointP004RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP004Factor2548 edgeMidpointP004Center2548) =
        edgeMidpointP004Rounded2549 := by
  cbv

theorem edgeMidpointP004RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP004Rounded2549‖ ≤ edgeMidpointP004Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP004Factor2548
      edgeMidpointP004Center2548)
  rw [edgeMidpointP004RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP004Factor2548 * embedPair2542 edgeMidpointP004Center2548)
    (embedPair2542 edgeMidpointP004Rounded2549)).trans (add_le_add
        edgeMidpointP004DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP004Factor2548, edgeMidpointP004Error2548,
      rounding2542,
      edgeMidpointP004Radius2549]

theorem edgeMidpointP004DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩ edgeMidpointPosition2548‖ ≤ 1 :=
        by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP004Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP004RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP004Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP004Radius2549, pairMagnitude2542, edgeMidpointP004Rounded2549]

def edgeMidpointP005Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP005Radius2549 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem edgeMidpointP005RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP005Factor2548 edgeMidpointP005Center2548) =
        edgeMidpointP005Rounded2549 := by
  cbv

theorem edgeMidpointP005RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP005Rounded2549‖ ≤ edgeMidpointP005Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP005Factor2548
      edgeMidpointP005Center2548)
  rw [edgeMidpointP005RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP005Factor2548 * embedPair2542 edgeMidpointP005Center2548)
    (embedPair2542 edgeMidpointP005Rounded2549)).trans (add_le_add
        edgeMidpointP005DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP005Factor2548, edgeMidpointP005Error2548,
      rounding2542,
      edgeMidpointP005Radius2549]

theorem edgeMidpointP005DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩ edgeMidpointPosition2548‖ ≤ 1 :=
        by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP005Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP005RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP005Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP005Radius2549, pairMagnitude2542, edgeMidpointP005Rounded2549]

def edgeMidpointP006Rounded2549 : RatPair2542 :=
  (((1 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP006Radius2549 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem edgeMidpointP006RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP006Factor2548 edgeMidpointP006Center2548) =
        edgeMidpointP006Rounded2549 := by
  cbv

theorem edgeMidpointP006RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP006Rounded2549‖ ≤ edgeMidpointP006Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP006Factor2548
      edgeMidpointP006Center2548)
  rw [edgeMidpointP006RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP006Factor2548 * embedPair2542 edgeMidpointP006Center2548)
    (embedPair2542 edgeMidpointP006Rounded2549)).trans (add_le_add
        edgeMidpointP006DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP006Factor2548, edgeMidpointP006Error2548,
      rounding2542,
      edgeMidpointP006Radius2549]

theorem edgeMidpointP006DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩ edgeMidpointPosition2548‖ ≤ 1 :=
        by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP006Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP006RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP006Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP006Radius2549, pairMagnitude2542, edgeMidpointP006Rounded2549]

def edgeMidpointP007Rounded2549 : RatPair2542 :=
  (((1852709455279 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP007Radius2549 : ℝ := ((1099646212197 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem edgeMidpointP007RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP007Factor2548 edgeMidpointP007Center2548) =
        edgeMidpointP007Rounded2549 := by
  cbv

theorem edgeMidpointP007RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP007Rounded2549‖ ≤ edgeMidpointP007Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP007Factor2548
      edgeMidpointP007Center2548)
  rw [edgeMidpointP007RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP007Factor2548 * embedPair2542 edgeMidpointP007Center2548)
    (embedPair2542 edgeMidpointP007Rounded2549)).trans (add_le_add
        edgeMidpointP007DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP007Factor2548, edgeMidpointP007Error2548,
      rounding2542,
      edgeMidpointP007Radius2549]

theorem edgeMidpointP007DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩ edgeMidpointPosition2548‖ ≤ 1 :=
        by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP007Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP007RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP007Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP007Radius2549, pairMagnitude2542, edgeMidpointP007Rounded2549]

def edgeMidpointP008Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP008Radius2549 : ℝ := ((2223573724293 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem edgeMidpointP008RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP008Factor2548 edgeMidpointP008Center2548) =
        edgeMidpointP008Rounded2549 := by
  cbv

theorem edgeMidpointP008RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP008Rounded2549‖ ≤ edgeMidpointP008Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP008Factor2548
      edgeMidpointP008Center2548)
  rw [edgeMidpointP008RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP008Factor2548 * embedPair2542 edgeMidpointP008Center2548)
    (embedPair2542 edgeMidpointP008Rounded2549)).trans (add_le_add
        edgeMidpointP008DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP008Factor2548, edgeMidpointP008Error2548,
      rounding2542,
      edgeMidpointP008Radius2549]

theorem edgeMidpointP008DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩ edgeMidpointPosition2548‖ ≤ 1 :=
        by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP008Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP008RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP008Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP008Radius2549, pairMagnitude2542, edgeMidpointP008Rounded2549]

def edgeMidpointP009Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP009Radius2549 : ℝ := ((1111786863637 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem edgeMidpointP009RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP009Factor2548 edgeMidpointP009Center2548) =
        edgeMidpointP009Rounded2549 := by
  cbv

theorem edgeMidpointP009RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP009Rounded2549‖ ≤ edgeMidpointP009Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP009Factor2548
      edgeMidpointP009Center2548)
  rw [edgeMidpointP009RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP009Factor2548 * embedPair2542 edgeMidpointP009Center2548)
    (embedPair2542 edgeMidpointP009Rounded2549)).trans (add_le_add
        edgeMidpointP009DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP009Factor2548, edgeMidpointP009Error2548,
      rounding2542,
      edgeMidpointP009Radius2549]

theorem edgeMidpointP009DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩ edgeMidpointPosition2548‖ ≤ 1 :=
        by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP009Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP009RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP009Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP009Radius2549, pairMagnitude2542, edgeMidpointP009Rounded2549]

def edgeMidpointP010Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP010Radius2549 : ℝ := ((2223573729001 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem edgeMidpointP010RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP010Factor2548 edgeMidpointP010Center2548) =
        edgeMidpointP010Rounded2549 := by
  cbv

theorem edgeMidpointP010RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP010Rounded2549‖ ≤ edgeMidpointP010Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP010Factor2548
      edgeMidpointP010Center2548)
  rw [edgeMidpointP010RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP010Factor2548 * embedPair2542 edgeMidpointP010Center2548)
    (embedPair2542 edgeMidpointP010Rounded2549)).trans (add_le_add
        edgeMidpointP010DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP010Factor2548, edgeMidpointP010Error2548,
      rounding2542,
      edgeMidpointP010Radius2549]

theorem edgeMidpointP010DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP010Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP010RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP010Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP010Radius2549, pairMagnitude2542, edgeMidpointP010Rounded2549]

def edgeMidpointP011Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP011Radius2549 : ℝ := ((277946716269 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem edgeMidpointP011RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP011Factor2548 edgeMidpointP011Center2548) =
        edgeMidpointP011Rounded2549 := by
  cbv

theorem edgeMidpointP011RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP011Rounded2549‖ ≤ edgeMidpointP011Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP011Factor2548
      edgeMidpointP011Center2548)
  rw [edgeMidpointP011RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP011Factor2548 * embedPair2542 edgeMidpointP011Center2548)
    (embedPair2542 edgeMidpointP011Rounded2549)).trans (add_le_add
        edgeMidpointP011DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP011Factor2548, edgeMidpointP011Error2548,
      rounding2542,
      edgeMidpointP011Radius2549]

theorem edgeMidpointP011DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP011Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP011RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP011Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP011Radius2549, pairMagnitude2542, edgeMidpointP011Rounded2549]

def edgeMidpointP012Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP012Radius2549 : ℝ := ((138973358209 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem edgeMidpointP012RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP012Factor2548 edgeMidpointP012Center2548) =
        edgeMidpointP012Rounded2549 := by
  cbv

theorem edgeMidpointP012RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP012Rounded2549‖ ≤ edgeMidpointP012Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP012Factor2548
      edgeMidpointP012Center2548)
  rw [edgeMidpointP012RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP012Factor2548 * embedPair2542 edgeMidpointP012Center2548)
    (embedPair2542 edgeMidpointP012Rounded2549)).trans (add_le_add
        edgeMidpointP012DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP012Factor2548, edgeMidpointP012Error2548,
      rounding2542,
      edgeMidpointP012Radius2549]

theorem edgeMidpointP012DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP012Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP012RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP012Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP012Radius2549, pairMagnitude2542, edgeMidpointP012Rounded2549]

def edgeMidpointP013Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP013Radius2549 : ℝ := ((1111786866215 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem edgeMidpointP013RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP013Factor2548 edgeMidpointP013Center2548) =
        edgeMidpointP013Rounded2549 := by
  cbv

theorem edgeMidpointP013RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP013Rounded2549‖ ≤ edgeMidpointP013Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP013Factor2548
      edgeMidpointP013Center2548)
  rw [edgeMidpointP013RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP013Factor2548 * embedPair2542 edgeMidpointP013Center2548)
    (embedPair2542 edgeMidpointP013Rounded2549)).trans (add_le_add
        edgeMidpointP013DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP013Factor2548, edgeMidpointP013Error2548,
      rounding2542,
      edgeMidpointP013Radius2549]

theorem edgeMidpointP013DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP013Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP013RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP013Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP013Radius2549, pairMagnitude2542, edgeMidpointP013Rounded2549]

def edgeMidpointP014Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP014Radius2549 : ℝ := ((2223573734443 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem edgeMidpointP014RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP014Factor2548 edgeMidpointP014Center2548) =
        edgeMidpointP014Rounded2549 := by
  cbv

theorem edgeMidpointP014RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP014Rounded2549‖ ≤ edgeMidpointP014Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP014Factor2548
      edgeMidpointP014Center2548)
  rw [edgeMidpointP014RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP014Factor2548 * embedPair2542 edgeMidpointP014Center2548)
    (embedPair2542 edgeMidpointP014Rounded2549)).trans (add_le_add
        edgeMidpointP014DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP014Factor2548, edgeMidpointP014Error2548,
      rounding2542,
      edgeMidpointP014Radius2549]

theorem edgeMidpointP014DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP014Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP014RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP014Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP014Radius2549, pairMagnitude2542, edgeMidpointP014Rounded2549]

def edgeMidpointP015Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP015Radius2549 : ℝ := ((2223573735885 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem edgeMidpointP015RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP015Factor2548 edgeMidpointP015Center2548) =
        edgeMidpointP015Rounded2549 := by
  cbv

theorem edgeMidpointP015RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP015Rounded2549‖ ≤ edgeMidpointP015Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP015Factor2548
      edgeMidpointP015Center2548)
  rw [edgeMidpointP015RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP015Factor2548 * embedPair2542 edgeMidpointP015Center2548)
    (embedPair2542 edgeMidpointP015Rounded2549)).trans (add_le_add
        edgeMidpointP015DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP015Factor2548, edgeMidpointP015Error2548,
      rounding2542,
      edgeMidpointP015Radius2549]

theorem edgeMidpointP015DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP015Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP015RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP015Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP015Radius2549, pairMagnitude2542, edgeMidpointP015Rounded2549]

def edgeMidpointP016Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP016Radius2549 : ℝ := ((69486679279 : ℝ) /
        (4 * 10^40
        + 3556142965880123323311949751266331066368))

theorem edgeMidpointP016RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP016Factor2548 edgeMidpointP016Center2548) =
        edgeMidpointP016Rounded2549 := by
  cbv

theorem edgeMidpointP016RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP016Rounded2549‖ ≤ edgeMidpointP016Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP016Factor2548
      edgeMidpointP016Center2548)
  rw [edgeMidpointP016RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP016Factor2548 * embedPair2542 edgeMidpointP016Center2548)
    (embedPair2542 edgeMidpointP016Rounded2549)).trans (add_le_add
        edgeMidpointP016DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP016Factor2548, edgeMidpointP016Error2548,
      rounding2542,
      edgeMidpointP016Radius2549]

theorem edgeMidpointP016DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP016Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP016RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP016Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP016Radius2549, pairMagnitude2542, edgeMidpointP016Rounded2549]

def edgeMidpointP017Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP017Radius2549 : ℝ := ((277946717369 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem edgeMidpointP017RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP017Factor2548 edgeMidpointP017Center2548) =
        edgeMidpointP017Rounded2549 := by
  cbv

theorem edgeMidpointP017RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP017Rounded2549‖ ≤ edgeMidpointP017Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP017Factor2548
      edgeMidpointP017Center2548)
  rw [edgeMidpointP017RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP017Factor2548 * embedPair2542 edgeMidpointP017Center2548)
    (embedPair2542 edgeMidpointP017Rounded2549)).trans (add_le_add
        edgeMidpointP017DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP017Factor2548, edgeMidpointP017Error2548,
      rounding2542,
      edgeMidpointP017Radius2549]

theorem edgeMidpointP017DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP017Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP017RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP017Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP017Radius2549, pairMagnitude2542, edgeMidpointP017Rounded2549]

def edgeMidpointP018Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP018Radius2549 : ℝ := ((1111786869859 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem edgeMidpointP018RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP018Factor2548 edgeMidpointP018Center2548) =
        edgeMidpointP018Rounded2549 := by
  cbv

theorem edgeMidpointP018RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP018Rounded2549‖ ≤ edgeMidpointP018Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP018Factor2548
      edgeMidpointP018Center2548)
  rw [edgeMidpointP018RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP018Factor2548 * embedPair2542 edgeMidpointP018Center2548)
    (embedPair2542 edgeMidpointP018Rounded2549)).trans (add_le_add
        edgeMidpointP018DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP018Factor2548, edgeMidpointP018Error2548,
      rounding2542,
      edgeMidpointP018Radius2549]

theorem edgeMidpointP018DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP018Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP018RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP018Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP018Radius2549, pairMagnitude2542, edgeMidpointP018Rounded2549]

def edgeMidpointP019Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP019Radius2549 : ℝ := ((2223573741101 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem edgeMidpointP019RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP019Factor2548 edgeMidpointP019Center2548) =
        edgeMidpointP019Rounded2549 := by
  cbv

theorem edgeMidpointP019RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP019Rounded2549‖ ≤ edgeMidpointP019Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP019Factor2548
      edgeMidpointP019Center2548)
  rw [edgeMidpointP019RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP019Factor2548 * embedPair2542 edgeMidpointP019Center2548)
    (embedPair2542 edgeMidpointP019Rounded2549)).trans (add_le_add
        edgeMidpointP019DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP019Factor2548, edgeMidpointP019Error2548,
      rounding2542,
      edgeMidpointP019Radius2549]

theorem edgeMidpointP019DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP019Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP019RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP019Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP019Radius2549, pairMagnitude2542, edgeMidpointP019Rounded2549]

def edgeMidpointP020Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP020Radius2549 : ℝ := ((1111786871303 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem edgeMidpointP020RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP020Factor2548 edgeMidpointP020Center2548) =
        edgeMidpointP020Rounded2549 := by
  cbv

theorem edgeMidpointP020RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP020Rounded2549‖ ≤ edgeMidpointP020Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP020Factor2548
      edgeMidpointP020Center2548)
  rw [edgeMidpointP020RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP020Factor2548 * embedPair2542 edgeMidpointP020Center2548)
    (embedPair2542 edgeMidpointP020Rounded2549)).trans (add_le_add
        edgeMidpointP020DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP020Factor2548, edgeMidpointP020Error2548,
      rounding2542,
      edgeMidpointP020Radius2549]

theorem edgeMidpointP020DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP020Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP020RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP020Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP020Radius2549, pairMagnitude2542, edgeMidpointP020Rounded2549]

def edgeMidpointP021Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP021Radius2549 : ℝ := ((2223573743861 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem edgeMidpointP021RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP021Factor2548 edgeMidpointP021Center2548) =
        edgeMidpointP021Rounded2549 := by
  cbv

theorem edgeMidpointP021RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP021Rounded2549‖ ≤ edgeMidpointP021Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP021Factor2548
      edgeMidpointP021Center2548)
  rw [edgeMidpointP021RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP021Factor2548 * embedPair2542 edgeMidpointP021Center2548)
    (embedPair2542 edgeMidpointP021Rounded2549)).trans (add_le_add
        edgeMidpointP021DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP021Factor2548, edgeMidpointP021Error2548,
      rounding2542,
      edgeMidpointP021Radius2549]

theorem edgeMidpointP021DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP021Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP021RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP021Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP021Radius2549, pairMagnitude2542, edgeMidpointP021Rounded2549]

def edgeMidpointP022Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP022Radius2549 : ℝ := ((277946718063 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem edgeMidpointP022RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP022Factor2548 edgeMidpointP022Center2548) =
        edgeMidpointP022Rounded2549 := by
  cbv

theorem edgeMidpointP022RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP022Rounded2549‖ ≤ edgeMidpointP022Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP022Factor2548
      edgeMidpointP022Center2548)
  rw [edgeMidpointP022RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP022Factor2548 * embedPair2542 edgeMidpointP022Center2548)
    (embedPair2542 edgeMidpointP022Rounded2549)).trans (add_le_add
        edgeMidpointP022DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP022Factor2548, edgeMidpointP022Error2548,
      rounding2542,
      edgeMidpointP022Radius2549]

theorem edgeMidpointP022DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP022Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP022RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP022Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP022Radius2549, pairMagnitude2542, edgeMidpointP022Rounded2549]

def edgeMidpointP023Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP023Radius2549 : ℝ := ((555893436589 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem edgeMidpointP023RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP023Factor2548 edgeMidpointP023Center2548) =
        edgeMidpointP023Rounded2549 := by
  cbv

theorem edgeMidpointP023RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP023Rounded2549‖ ≤ edgeMidpointP023Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP023Factor2548
      edgeMidpointP023Center2548)
  rw [edgeMidpointP023RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP023Factor2548 * embedPair2542 edgeMidpointP023Center2548)
    (embedPair2542 edgeMidpointP023Rounded2549)).trans (add_le_add
        edgeMidpointP023DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP023Factor2548, edgeMidpointP023Error2548,
      rounding2542,
      edgeMidpointP023Radius2549]

theorem edgeMidpointP023DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP023Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP023RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP023Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP023Radius2549, pairMagnitude2542, edgeMidpointP023Rounded2549]

def edgeMidpointP024Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP024Radius2549 : ℝ := ((277946718401 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem edgeMidpointP024RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP024Factor2548 edgeMidpointP024Center2548) =
        edgeMidpointP024Rounded2549 := by
  cbv

theorem edgeMidpointP024RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP024Rounded2549‖ ≤ edgeMidpointP024Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP024Factor2548
      edgeMidpointP024Center2548)
  rw [edgeMidpointP024RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP024Factor2548 * embedPair2542 edgeMidpointP024Center2548)
    (embedPair2542 edgeMidpointP024Rounded2549)).trans (add_le_add
        edgeMidpointP024DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP024Factor2548, edgeMidpointP024Error2548,
      rounding2542,
      edgeMidpointP024Radius2549]

theorem edgeMidpointP024DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP024Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP024RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP024Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP024Radius2549, pairMagnitude2542, edgeMidpointP024Rounded2549]

def edgeMidpointP025Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP025Radius2549 : ℝ := ((2223573748275 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem edgeMidpointP025RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP025Factor2548 edgeMidpointP025Center2548) =
        edgeMidpointP025Rounded2549 := by
  cbv

theorem edgeMidpointP025RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP025Rounded2549‖ ≤ edgeMidpointP025Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP025Factor2548
      edgeMidpointP025Center2548)
  rw [edgeMidpointP025RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP025Factor2548 * embedPair2542 edgeMidpointP025Center2548)
    (embedPair2542 edgeMidpointP025Rounded2549)).trans (add_le_add
        edgeMidpointP025DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP025Factor2548, edgeMidpointP025Error2548,
      rounding2542,
      edgeMidpointP025Radius2549]

theorem edgeMidpointP025DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP025Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP025RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP025Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP025Radius2549, pairMagnitude2542, edgeMidpointP025Rounded2549]

def edgeMidpointP026Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP026Radius2549 : ℝ := ((1111786874683 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem edgeMidpointP026RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP026Factor2548 edgeMidpointP026Center2548) =
        edgeMidpointP026Rounded2549 := by
  cbv

theorem edgeMidpointP026RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP026Rounded2549‖ ≤ edgeMidpointP026Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP026Factor2548
      edgeMidpointP026Center2548)
  rw [edgeMidpointP026RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP026Factor2548 * embedPair2542 edgeMidpointP026Center2548)
    (embedPair2542 edgeMidpointP026Rounded2549)).trans (add_le_add
        edgeMidpointP026DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP026Factor2548, edgeMidpointP026Error2548,
      rounding2542,
      edgeMidpointP026Radius2549]

theorem edgeMidpointP026DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP026Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP026RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP026Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP026Radius2549, pairMagnitude2542, edgeMidpointP026Rounded2549]

def edgeMidpointP027Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP027Radius2549 : ℝ := ((555893437735 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem edgeMidpointP027RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP027Factor2548 edgeMidpointP027Center2548) =
        edgeMidpointP027Rounded2549 := by
  cbv

theorem edgeMidpointP027RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP027Rounded2549‖ ≤ edgeMidpointP027Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP027Factor2548
      edgeMidpointP027Center2548)
  rw [edgeMidpointP027RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP027Factor2548 * embedPair2542 edgeMidpointP027Center2548)
    (embedPair2542 edgeMidpointP027Rounded2549)).trans (add_le_add
        edgeMidpointP027DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP027Factor2548, edgeMidpointP027Error2548,
      rounding2542,
      edgeMidpointP027Radius2549]

theorem edgeMidpointP027DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP027Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP027RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP027Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP027Radius2549, pairMagnitude2542, edgeMidpointP027Rounded2549]

def edgeMidpointP028Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP028Radius2549 : ℝ := ((555893437891 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem edgeMidpointP028RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP028Factor2548 edgeMidpointP028Center2548) =
        edgeMidpointP028Rounded2549 := by
  cbv

theorem edgeMidpointP028RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP028Rounded2549‖ ≤ edgeMidpointP028Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP028Factor2548
      edgeMidpointP028Center2548)
  rw [edgeMidpointP028RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP028Factor2548 * embedPair2542 edgeMidpointP028Center2548)
    (embedPair2542 edgeMidpointP028Rounded2549)).trans (add_le_add
        edgeMidpointP028DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP028Factor2548, edgeMidpointP028Error2548,
      rounding2542,
      edgeMidpointP028Radius2549]

theorem edgeMidpointP028DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP028Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP028RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP028Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP028Radius2549, pairMagnitude2542, edgeMidpointP028Rounded2549]

def edgeMidpointP029Rounded2549 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def edgeMidpointP029Radius2549 : ℝ := ((2223573752513 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem edgeMidpointP029RoundCompute2549 :
    pairRound2542 (pairMul2542 edgeMidpointP029Factor2548 edgeMidpointP029Center2548) =
        edgeMidpointP029Rounded2549 := by
  cbv

theorem edgeMidpointP029RoundedError2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩ edgeMidpointPosition2548 -
      embedPair2542 edgeMidpointP029Rounded2549‖ ≤ edgeMidpointP029Radius2549 := by
  have hr := embedPair_round_error2542 (pairMul2542 edgeMidpointP029Factor2548
      edgeMidpointP029Center2548)
  rw [edgeMidpointP029RoundCompute2549, embedPair_mul2542] at hr
  have h := (edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP029Factor2548 * embedPair2542 edgeMidpointP029Center2548)
    (embedPair2542 edgeMidpointP029Rounded2549)).trans (add_le_add
        edgeMidpointP029DerivativeError2548 hr)
  apply h.trans
  norm_num [pairMagnitude2542, edgeMidpointP029Factor2548, edgeMidpointP029Error2548,
      rounding2542,
      edgeMidpointP029Radius2549]

theorem edgeMidpointP029DerivativeNorm2549 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩ edgeMidpointPosition2548‖ ≤ 1
        := by
  have h := edgeMidpoint_triangle2549
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩ edgeMidpointPosition2548)
    (embedPair2542 edgeMidpointP029Rounded2549) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add edgeMidpointP029RoundedError2549 (embedPair_magnitude2542
      edgeMidpointP029Rounded2549))
  apply h'.trans
  norm_num [edgeMidpointP029Radius2549, pairMagnitude2542, edgeMidpointP029Rounded2549]

noncomputable def edgeSignedMidpointValue2549 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 edgeMidpointP000Rounded2549
  | 1 => embedPair2542 edgeMidpointP001Rounded2549
  | 2 => embedPair2542 edgeMidpointP002Rounded2549
  | 3 => embedPair2542 edgeMidpointP003Rounded2549
  | 4 => embedPair2542 edgeMidpointP004Rounded2549
  | 5 => embedPair2542 edgeMidpointP005Rounded2549
  | 6 => embedPair2542 edgeMidpointP006Rounded2549
  | 7 => embedPair2542 edgeMidpointP007Rounded2549
  | 8 => embedPair2542 edgeMidpointP008Rounded2549
  | 9 => embedPair2542 edgeMidpointP009Rounded2549
  | 10 => embedPair2542 edgeMidpointP010Rounded2549
  | 11 => embedPair2542 edgeMidpointP011Rounded2549
  | 12 => embedPair2542 edgeMidpointP012Rounded2549
  | 13 => embedPair2542 edgeMidpointP013Rounded2549
  | 14 => embedPair2542 edgeMidpointP014Rounded2549
  | 15 => embedPair2542 edgeMidpointP015Rounded2549
  | 16 => embedPair2542 edgeMidpointP016Rounded2549
  | 17 => embedPair2542 edgeMidpointP017Rounded2549
  | 18 => embedPair2542 edgeMidpointP018Rounded2549
  | 19 => embedPair2542 edgeMidpointP019Rounded2549
  | 20 => embedPair2542 edgeMidpointP020Rounded2549
  | 21 => embedPair2542 edgeMidpointP021Rounded2549
  | 22 => embedPair2542 edgeMidpointP022Rounded2549
  | 23 => embedPair2542 edgeMidpointP023Rounded2549
  | 24 => embedPair2542 edgeMidpointP024Rounded2549
  | 25 => embedPair2542 edgeMidpointP025Rounded2549
  | 26 => embedPair2542 edgeMidpointP026Rounded2549
  | 27 => embedPair2542 edgeMidpointP027Rounded2549
  | 28 => embedPair2542 edgeMidpointP028Rounded2549
  | 29 => embedPair2542 edgeMidpointP029Rounded2549
  | _ => 0

noncomputable def edgeSignedMidpointError2549 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => edgeMidpointP000Radius2549
  | 1 => edgeMidpointP001Radius2549
  | 2 => edgeMidpointP002Radius2549
  | 3 => edgeMidpointP003Radius2549
  | 4 => edgeMidpointP004Radius2549
  | 5 => edgeMidpointP005Radius2549
  | 6 => edgeMidpointP006Radius2549
  | 7 => edgeMidpointP007Radius2549
  | 8 => edgeMidpointP008Radius2549
  | 9 => edgeMidpointP009Radius2549
  | 10 => edgeMidpointP010Radius2549
  | 11 => edgeMidpointP011Radius2549
  | 12 => edgeMidpointP012Radius2549
  | 13 => edgeMidpointP013Radius2549
  | 14 => edgeMidpointP014Radius2549
  | 15 => edgeMidpointP015Radius2549
  | 16 => edgeMidpointP016Radius2549
  | 17 => edgeMidpointP017Radius2549
  | 18 => edgeMidpointP018Radius2549
  | 19 => edgeMidpointP019Radius2549
  | 20 => edgeMidpointP020Radius2549
  | 21 => edgeMidpointP021Radius2549
  | 22 => edgeMidpointP022Radius2549
  | 23 => edgeMidpointP023Radius2549
  | 24 => edgeMidpointP024Radius2549
  | 25 => edgeMidpointP025Radius2549
  | 26 => edgeMidpointP026Radius2549
  | 27 => edgeMidpointP027Radius2549
  | 28 => edgeMidpointP028Radius2549
  | 29 => edgeMidpointP029Radius2549
  | _ => 0

theorem edgeSignedMidpointExpError2549 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i edgeMidpointPosition2548 -
        edgeSignedMidpointValue2549 i‖ ≤ edgeSignedMidpointError2549 i := by
  fin_cases i
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP000RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP001RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP002RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP003RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP004RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP005RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP006RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP007RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP008RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP009RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP010RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP011RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP012RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP013RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP014RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP015RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP016RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP017RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP018RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP019RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP020RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP021RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP022RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP023RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP024RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP025RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP026RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP027RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP028RoundedError2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP029RoundedError2549

theorem edgeSignedMidpointUnitNorm2549 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤ 1 := by
  fin_cases i
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP000DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP001DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP002DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP003DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP004DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP005DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP006DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP007DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP008DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP009DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP010DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP011DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP012DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP013DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP014DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP015DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP016DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP017DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP018DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP019DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP020DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP021DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP022DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP023DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP024DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP025DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP026DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP027DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP028DerivativeNorm2549
  · simpa only [edgeSignedMidpointValue2549, edgeSignedMidpointError2549] using
      edgeMidpointP029DerivativeNorm2549

noncomputable def edgeSignedMidpointSum2549 : ℂ := ⟨(((-(((3799 * 10^40
        + 6685605077440837126035958386636642668854) * 10^40
        + 3067130214842208459058169478650349255097) * 10^40
        + 7228261301618323694781161573608753856707)) : ℝ) /
        (((21661481 * 10^40
        + 9853188660904563608136178414330971646513) * 10^40
        + 7356699351937172355172896723145017999980) * 10^40
        + 47688590453885868835635965404913860608)),
    (((-(((131 * 10^40
        + 5058006603608054653560648572876380667654) * 10^40
        + 6463026732528082206085874357707970195372) * 10^40
        + 8033968005117630904243217967921675496395)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216))⟩

noncomputable def edgeSignedMidpointUpper2549 : ℝ := ((8777 : ℝ) /
        50000000)

theorem edgeSignedMidpointSum_eq2549 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * edgeSignedMidpointValue2549 i) =
      edgeSignedMidpointSum2549 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, edgeSignedMidpointValue2549,
      edgeSignedMidpointSum2549, embedPair2542, edgeMidpointP000Rounded2549,
      edgeMidpointP001Rounded2549,
      edgeMidpointP002Rounded2549,
      edgeMidpointP003Rounded2549,
      edgeMidpointP004Rounded2549,
      edgeMidpointP005Rounded2549,
      edgeMidpointP006Rounded2549,
      edgeMidpointP007Rounded2549,
      edgeMidpointP008Rounded2549,
      edgeMidpointP009Rounded2549,
      edgeMidpointP010Rounded2549,
      edgeMidpointP011Rounded2549,
      edgeMidpointP012Rounded2549,
      edgeMidpointP013Rounded2549,
      edgeMidpointP014Rounded2549,
      edgeMidpointP015Rounded2549,
      edgeMidpointP016Rounded2549,
      edgeMidpointP017Rounded2549,
      edgeMidpointP018Rounded2549,
      edgeMidpointP019Rounded2549,
      edgeMidpointP020Rounded2549,
      edgeMidpointP021Rounded2549,
      edgeMidpointP022Rounded2549,
      edgeMidpointP023Rounded2549,
      edgeMidpointP024Rounded2549,
      edgeMidpointP025Rounded2549,
      edgeMidpointP026Rounded2549,
      edgeMidpointP027Rounded2549,
      edgeMidpointP028Rounded2549,
      edgeMidpointP029Rounded2549, Complex.mul_re, Complex.mul_im]

theorem edgeSignedMidpointSum_norm2549 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * edgeSignedMidpointValue2549 i‖ ≤ ((2193 : ℝ) /
        12500000) := by
  rw [edgeSignedMidpointSum_eq2549]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [edgeSignedMidpointSum2549]

theorem edgeSignedMidpointCharge2549 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * edgeSignedMidpointError2549 i) ≤ (1 : ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, edgeSignedMidpointError2549,
      edgeMidpointP000Radius2549,
      edgeMidpointP001Radius2549,
      edgeMidpointP002Radius2549,
      edgeMidpointP003Radius2549,
      edgeMidpointP004Radius2549,
      edgeMidpointP005Radius2549,
      edgeMidpointP006Radius2549,
      edgeMidpointP007Radius2549,
      edgeMidpointP008Radius2549,
      edgeMidpointP009Radius2549,
      edgeMidpointP010Radius2549,
      edgeMidpointP011Radius2549,
      edgeMidpointP012Radius2549,
      edgeMidpointP013Radius2549,
      edgeMidpointP014Radius2549,
      edgeMidpointP015Radius2549,
      edgeMidpointP016Radius2549,
      edgeMidpointP017Radius2549,
      edgeMidpointP018Radius2549,
      edgeMidpointP019Radius2549,
      edgeMidpointP020Radius2549,
      edgeMidpointP021Radius2549,
      edgeMidpointP022Radius2549,
      edgeMidpointP023Radius2549,
      edgeMidpointP024Radius2549,
      edgeMidpointP025Radius2549,
      edgeMidpointP026Radius2549,
      edgeMidpointP027Radius2549,
      edgeMidpointP028Radius2549,
      edgeMidpointP029Radius2549]

theorem edgeSignedMidpointUpper_le2549 :
    signedJetUpper2539 2 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 edgeMidpointPosition2548 ≤ edgeSignedMidpointUpper2549 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * edgeSignedMidpointValue2549 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * edgeSignedMidpointError2549 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (edgeSignedMidpointExpError2549 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (edgeSignedMidpointUnitNorm2549 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i edgeMidpointPosition2548‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 edgeSignedMidpointUpper2549
  linarith [edgeSignedMidpointSum_norm2549, edgeSignedMidpointCharge2549]

theorem weightedPhysical_edge_midpoint_le2549 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        edgeMidpointPosition2548‖ ≤
      edgeSignedMidpointUpper2549 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        edgeMidpointPosition2548
  exact h.trans edgeSignedMidpointUpper_le2549

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.edgeSignedMidpointExpError2549
#print axioms ConnesWeilRH.Dev.edgeSignedMidpointSum_eq2549
#print axioms ConnesWeilRH.Dev.edgeSignedMidpointCharge2549
#print axioms ConnesWeilRH.Dev.edgeSignedMidpointUpper_le2549
#print axioms ConnesWeilRH.Dev.weightedPhysical_edge_midpoint_le2549
