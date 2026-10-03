import ConnesWeilRH.Dev.C1RouteANeighborMidpoint2557

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem neighborMidpoint_triangle2557 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def neighborMidpointP000Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP000Radius2557 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem neighborMidpointP000RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP000Factor2557 neighborMidpointP000Center2557) =
        neighborMidpointP000Rounded2557 := by
  cbv

theorem neighborMidpointP000RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP000Rounded2557‖ ≤ neighborMidpointP000Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP000Factor2557
      neighborMidpointP000Center2557)
  rw [neighborMidpointP000RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP000Factor2557 * embedPair2542 neighborMidpointP000Center2557)
    (embedPair2542 neighborMidpointP000Rounded2557)).trans (add_le_add
        neighborMidpointP000DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP000Factor2557, neighborMidpointP000Error2557,
      rounding2542,
      neighborMidpointP000Radius2557]

theorem neighborMidpointP000DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP000Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP000RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP000Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP000Radius2557, pairMagnitude2542, neighborMidpointP000Rounded2557]

def neighborMidpointP001Rounded2557 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP001Radius2557 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem neighborMidpointP001RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP001Factor2557 neighborMidpointP001Center2557) =
        neighborMidpointP001Rounded2557 := by
  cbv

theorem neighborMidpointP001RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP001Rounded2557‖ ≤ neighborMidpointP001Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP001Factor2557
      neighborMidpointP001Center2557)
  rw [neighborMidpointP001RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP001Factor2557 * embedPair2542 neighborMidpointP001Center2557)
    (embedPair2542 neighborMidpointP001Rounded2557)).trans (add_le_add
        neighborMidpointP001DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP001Factor2557, neighborMidpointP001Error2557,
      rounding2542,
      neighborMidpointP001Radius2557]

theorem neighborMidpointP001DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP001Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP001RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP001Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP001Radius2557, pairMagnitude2542, neighborMidpointP001Rounded2557]

def neighborMidpointP002Rounded2557 : RatPair2542 :=
  (((1467053 : ℚ) /
        1267650600228229401496703205376),
    (((-257549) : ℚ) /
        316912650057057350374175801344))

noncomputable def neighborMidpointP002Radius2557 : ℝ := ((2199023262581 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem neighborMidpointP002RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP002Factor2557 neighborMidpointP002Center2557) =
        neighborMidpointP002Rounded2557 := by
  cbv

theorem neighborMidpointP002RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP002Rounded2557‖ ≤ neighborMidpointP002Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP002Factor2557
      neighborMidpointP002Center2557)
  rw [neighborMidpointP002RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP002Factor2557 * embedPair2542 neighborMidpointP002Center2557)
    (embedPair2542 neighborMidpointP002Rounded2557)).trans (add_le_add
        neighborMidpointP002DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP002Factor2557, neighborMidpointP002Error2557,
      rounding2542,
      neighborMidpointP002Radius2557]

theorem neighborMidpointP002DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP002Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP002RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP002Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP002Radius2557, pairMagnitude2542, neighborMidpointP002Rounded2557]

def neighborMidpointP003Rounded2557 : RatPair2542 :=
  (((15521349487099 : ℚ) /
        1267650600228229401496703205376),
    ((4671767380427 : ℚ) /
        1267650600228229401496703205376))

noncomputable def neighborMidpointP003Radius2557 : ℝ := ((2279098304669 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem neighborMidpointP003RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP003Factor2557 neighborMidpointP003Center2557) =
        neighborMidpointP003Rounded2557 := by
  cbv

theorem neighborMidpointP003RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP003Rounded2557‖ ≤ neighborMidpointP003Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP003Factor2557
      neighborMidpointP003Center2557)
  rw [neighborMidpointP003RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP003Factor2557 * embedPair2542 neighborMidpointP003Center2557)
    (embedPair2542 neighborMidpointP003Rounded2557)).trans (add_le_add
        neighborMidpointP003DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP003Factor2557, neighborMidpointP003Error2557,
      rounding2542,
      neighborMidpointP003Radius2557]

theorem neighborMidpointP003DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP003Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP003RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP003Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP003Radius2557, pairMagnitude2542, neighborMidpointP003Rounded2557]

def neighborMidpointP004Rounded2557 : RatPair2542 :=
  (((5946968411906771 : ℚ) /
        1267650600228229401496703205376),
    (((-133952017126263) : ℚ) /
        39614081257132168796771975168))

noncomputable def neighborMidpointP004Radius2557 : ℝ := ((34820496784661 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem neighborMidpointP004RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP004Factor2557 neighborMidpointP004Center2557) =
        neighborMidpointP004Rounded2557 := by
  cbv

theorem neighborMidpointP004RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP004Rounded2557‖ ≤ neighborMidpointP004Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP004Factor2557
      neighborMidpointP004Center2557)
  rw [neighborMidpointP004RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP004Factor2557 * embedPair2542 neighborMidpointP004Center2557)
    (embedPair2542 neighborMidpointP004Rounded2557)).trans (add_le_add
        neighborMidpointP004DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP004Factor2557, neighborMidpointP004Error2557,
      rounding2542,
      neighborMidpointP004Radius2557]

theorem neighborMidpointP004DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP004Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP004RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP004Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP004Radius2557, pairMagnitude2542, neighborMidpointP004Rounded2557]

def neighborMidpointP005Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP005Radius2557 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem neighborMidpointP005RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP005Factor2557 neighborMidpointP005Center2557) =
        neighborMidpointP005Rounded2557 := by
  cbv

theorem neighborMidpointP005RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP005Rounded2557‖ ≤ neighborMidpointP005Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP005Factor2557
      neighborMidpointP005Center2557)
  rw [neighborMidpointP005RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP005Factor2557 * embedPair2542 neighborMidpointP005Center2557)
    (embedPair2542 neighborMidpointP005Rounded2557)).trans (add_le_add
        neighborMidpointP005DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP005Factor2557, neighborMidpointP005Error2557,
      rounding2542,
      neighborMidpointP005Radius2557]

theorem neighborMidpointP005DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP005Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP005RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP005Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP005Radius2557, pairMagnitude2542, neighborMidpointP005Rounded2557]

def neighborMidpointP006Rounded2557 : RatPair2542 :=
  (((1 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP006Radius2557 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem neighborMidpointP006RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP006Factor2557 neighborMidpointP006Center2557) =
        neighborMidpointP006Rounded2557 := by
  cbv

theorem neighborMidpointP006RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP006Rounded2557‖ ≤ neighborMidpointP006Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP006Factor2557
      neighborMidpointP006Center2557)
  rw [neighborMidpointP006RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP006Factor2557 * embedPair2542 neighborMidpointP006Center2557)
    (embedPair2542 neighborMidpointP006Rounded2557)).trans (add_le_add
        neighborMidpointP006DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP006Factor2557, neighborMidpointP006Error2557,
      rounding2542,
      neighborMidpointP006Radius2557]

theorem neighborMidpointP006DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP006Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP006RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP006Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP006Radius2557, pairMagnitude2542, neighborMidpointP006Rounded2557]

def neighborMidpointP007Rounded2557 : RatPair2542 :=
  (((235452754951 : ℚ) /
        158456325028528675187087900672),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP007Radius2557 : ℝ := ((549824208591 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem neighborMidpointP007RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP007Factor2557 neighborMidpointP007Center2557) =
        neighborMidpointP007Rounded2557 := by
  cbv

theorem neighborMidpointP007RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP007Rounded2557‖ ≤ neighborMidpointP007Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP007Factor2557
      neighborMidpointP007Center2557)
  rw [neighborMidpointP007RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP007Factor2557 * embedPair2542 neighborMidpointP007Center2557)
    (embedPair2542 neighborMidpointP007Rounded2557)).trans (add_le_add
        neighborMidpointP007DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP007Factor2557, neighborMidpointP007Error2557,
      rounding2542,
      neighborMidpointP007Radius2557]

theorem neighborMidpointP007DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP007Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP007RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP007Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP007Radius2557, pairMagnitude2542, neighborMidpointP007Rounded2557]

def neighborMidpointP008Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP008Radius2557 : ℝ := ((549831567987 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem neighborMidpointP008RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP008Factor2557 neighborMidpointP008Center2557) =
        neighborMidpointP008Rounded2557 := by
  cbv

theorem neighborMidpointP008RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP008Rounded2557‖ ≤ neighborMidpointP008Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP008Factor2557
      neighborMidpointP008Center2557)
  rw [neighborMidpointP008RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP008Factor2557 * embedPair2542 neighborMidpointP008Center2557)
    (embedPair2542 neighborMidpointP008Rounded2557)).trans (add_le_add
        neighborMidpointP008DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP008Factor2557, neighborMidpointP008Error2557,
      rounding2542,
      neighborMidpointP008Radius2557]

theorem neighborMidpointP008DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP008Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP008RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP008Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP008Radius2557, pairMagnitude2542, neighborMidpointP008Rounded2557]

def neighborMidpointP009Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP009Radius2557 : ℝ := ((274915784035 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem neighborMidpointP009RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP009Factor2557 neighborMidpointP009Center2557) =
        neighborMidpointP009Rounded2557 := by
  cbv

theorem neighborMidpointP009RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP009Rounded2557‖ ≤ neighborMidpointP009Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP009Factor2557
      neighborMidpointP009Center2557)
  rw [neighborMidpointP009RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP009Factor2557 * embedPair2542 neighborMidpointP009Center2557)
    (embedPair2542 neighborMidpointP009Rounded2557)).trans (add_le_add
        neighborMidpointP009DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP009Factor2557, neighborMidpointP009Error2557,
      rounding2542,
      neighborMidpointP009Radius2557]

theorem neighborMidpointP009DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP009Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP009RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP009Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP009Radius2557, pairMagnitude2542, neighborMidpointP009Rounded2557]

def neighborMidpointP010Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP010Radius2557 : ℝ := ((2199326272471 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem neighborMidpointP010RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP010Factor2557 neighborMidpointP010Center2557) =
        neighborMidpointP010Rounded2557 := by
  cbv

theorem neighborMidpointP010RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP010Rounded2557‖ ≤ neighborMidpointP010Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP010Factor2557
      neighborMidpointP010Center2557)
  rw [neighborMidpointP010RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP010Factor2557 * embedPair2542 neighborMidpointP010Center2557)
    (embedPair2542 neighborMidpointP010Rounded2557)).trans (add_le_add
        neighborMidpointP010DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP010Factor2557, neighborMidpointP010Error2557,
      rounding2542,
      neighborMidpointP010Radius2557]

theorem neighborMidpointP010DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP010Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP010RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP010Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP010Radius2557, pairMagnitude2542, neighborMidpointP010Rounded2557]

def neighborMidpointP011Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP011Radius2557 : ℝ := ((2199326272599 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem neighborMidpointP011RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP011Factor2557 neighborMidpointP011Center2557) =
        neighborMidpointP011Rounded2557 := by
  cbv

theorem neighborMidpointP011RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP011Rounded2557‖ ≤ neighborMidpointP011Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP011Factor2557
      neighborMidpointP011Center2557)
  rw [neighborMidpointP011RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP011Factor2557 * embedPair2542 neighborMidpointP011Center2557)
    (embedPair2542 neighborMidpointP011Rounded2557)).trans (add_le_add
        neighborMidpointP011DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP011Factor2557, neighborMidpointP011Error2557,
      rounding2542,
      neighborMidpointP011Radius2557]

theorem neighborMidpointP011DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP011Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP011RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP011Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP011Radius2557, pairMagnitude2542, neighborMidpointP011Rounded2557]

def neighborMidpointP012Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP012Radius2557 : ℝ := ((549831568183 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem neighborMidpointP012RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP012Factor2557 neighborMidpointP012Center2557) =
        neighborMidpointP012Rounded2557 := by
  cbv

theorem neighborMidpointP012RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP012Rounded2557‖ ≤ neighborMidpointP012Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP012Factor2557
      neighborMidpointP012Center2557)
  rw [neighborMidpointP012RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP012Factor2557 * embedPair2542 neighborMidpointP012Center2557)
    (embedPair2542 neighborMidpointP012Rounded2557)).trans (add_le_add
        neighborMidpointP012DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP012Factor2557, neighborMidpointP012Error2557,
      rounding2542,
      neighborMidpointP012Radius2557]

theorem neighborMidpointP012DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP012Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP012RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP012Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP012Radius2557, pairMagnitude2542, neighborMidpointP012Rounded2557]

def neighborMidpointP013Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP013Radius2557 : ℝ := ((549831568213 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem neighborMidpointP013RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP013Factor2557 neighborMidpointP013Center2557) =
        neighborMidpointP013Rounded2557 := by
  cbv

theorem neighborMidpointP013RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP013Rounded2557‖ ≤ neighborMidpointP013Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP013Factor2557
      neighborMidpointP013Center2557)
  rw [neighborMidpointP013RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP013Factor2557 * embedPair2542 neighborMidpointP013Center2557)
    (embedPair2542 neighborMidpointP013Rounded2557)).trans (add_le_add
        neighborMidpointP013DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP013Factor2557, neighborMidpointP013Error2557,
      rounding2542,
      neighborMidpointP013Radius2557]

theorem neighborMidpointP013DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP013Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP013RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP013Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP013Radius2557, pairMagnitude2542, neighborMidpointP013Rounded2557]

def neighborMidpointP014Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP014Radius2557 : ℝ := ((549831568269 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem neighborMidpointP014RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP014Factor2557 neighborMidpointP014Center2557) =
        neighborMidpointP014Rounded2557 := by
  cbv

theorem neighborMidpointP014RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP014Rounded2557‖ ≤ neighborMidpointP014Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP014Factor2557
      neighborMidpointP014Center2557)
  rw [neighborMidpointP014RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP014Factor2557 * embedPair2542 neighborMidpointP014Center2557)
    (embedPair2542 neighborMidpointP014Rounded2557)).trans (add_le_add
        neighborMidpointP014DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP014Factor2557, neighborMidpointP014Error2557,
      rounding2542,
      neighborMidpointP014Radius2557]

theorem neighborMidpointP014DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP014Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP014RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP014Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP014Radius2557, pairMagnitude2542, neighborMidpointP014Rounded2557]

def neighborMidpointP015Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP015Radius2557 : ℝ := ((549831568309 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem neighborMidpointP015RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP015Factor2557 neighborMidpointP015Center2557) =
        neighborMidpointP015Rounded2557 := by
  cbv

theorem neighborMidpointP015RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP015Rounded2557‖ ≤ neighborMidpointP015Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP015Factor2557
      neighborMidpointP015Center2557)
  rw [neighborMidpointP015RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP015Factor2557 * embedPair2542 neighborMidpointP015Center2557)
    (embedPair2542 neighborMidpointP015Rounded2557)).trans (add_le_add
        neighborMidpointP015DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP015Factor2557, neighborMidpointP015Error2557,
      rounding2542,
      neighborMidpointP015Radius2557]

theorem neighborMidpointP015DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP015Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP015RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP015Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP015Radius2557, pairMagnitude2542, neighborMidpointP015Rounded2557]

def neighborMidpointP016Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP016Radius2557 : ℝ := ((274915784169 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem neighborMidpointP016RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP016Factor2557 neighborMidpointP016Center2557) =
        neighborMidpointP016Rounded2557 := by
  cbv

theorem neighborMidpointP016RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP016Rounded2557‖ ≤ neighborMidpointP016Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP016Factor2557
      neighborMidpointP016Center2557)
  rw [neighborMidpointP016RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP016Factor2557 * embedPair2542 neighborMidpointP016Center2557)
    (embedPair2542 neighborMidpointP016Rounded2557)).trans (add_le_add
        neighborMidpointP016DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP016Factor2557, neighborMidpointP016Error2557,
      rounding2542,
      neighborMidpointP016Radius2557]

theorem neighborMidpointP016DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP016Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP016RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP016Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP016Radius2557, pairMagnitude2542, neighborMidpointP016Rounded2557]

def neighborMidpointP017Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP017Radius2557 : ℝ := ((2199326273577 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem neighborMidpointP017RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP017Factor2557 neighborMidpointP017Center2557) =
        neighborMidpointP017Rounded2557 := by
  cbv

theorem neighborMidpointP017RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP017Rounded2557‖ ≤ neighborMidpointP017Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP017Factor2557
      neighborMidpointP017Center2557)
  rw [neighborMidpointP017RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP017Factor2557 * embedPair2542 neighborMidpointP017Center2557)
    (embedPair2542 neighborMidpointP017Rounded2557)).trans (add_le_add
        neighborMidpointP017DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP017Factor2557, neighborMidpointP017Error2557,
      rounding2542,
      neighborMidpointP017Radius2557]

theorem neighborMidpointP017DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP017Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP017RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP017Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP017Radius2557, pairMagnitude2542, neighborMidpointP017Rounded2557]

def neighborMidpointP018Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP018Radius2557 : ℝ := ((1099663136831 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem neighborMidpointP018RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP018Factor2557 neighborMidpointP018Center2557) =
        neighborMidpointP018Rounded2557 := by
  cbv

theorem neighborMidpointP018RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP018Rounded2557‖ ≤ neighborMidpointP018Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP018Factor2557
      neighborMidpointP018Center2557)
  rw [neighborMidpointP018RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP018Factor2557 * embedPair2542 neighborMidpointP018Center2557)
    (embedPair2542 neighborMidpointP018Rounded2557)).trans (add_le_add
        neighborMidpointP018DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP018Factor2557, neighborMidpointP018Error2557,
      rounding2542,
      neighborMidpointP018Radius2557]

theorem neighborMidpointP018DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP018Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP018RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP018Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP018Radius2557, pairMagnitude2542, neighborMidpointP018Rounded2557]

def neighborMidpointP019Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP019Radius2557 : ℝ := ((274915784227 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem neighborMidpointP019RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP019Factor2557 neighborMidpointP019Center2557) =
        neighborMidpointP019Rounded2557 := by
  cbv

theorem neighborMidpointP019RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP019Rounded2557‖ ≤ neighborMidpointP019Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP019Factor2557
      neighborMidpointP019Center2557)
  rw [neighborMidpointP019RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP019Factor2557 * embedPair2542 neighborMidpointP019Center2557)
    (embedPair2542 neighborMidpointP019Rounded2557)).trans (add_le_add
        neighborMidpointP019DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP019Factor2557, neighborMidpointP019Error2557,
      rounding2542,
      neighborMidpointP019Radius2557]

theorem neighborMidpointP019DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP019Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP019RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP019Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP019Radius2557, pairMagnitude2542, neighborMidpointP019Rounded2557]

def neighborMidpointP020Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP020Radius2557 : ℝ := ((2199326273983 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem neighborMidpointP020RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP020Factor2557 neighborMidpointP020Center2557) =
        neighborMidpointP020Rounded2557 := by
  cbv

theorem neighborMidpointP020RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP020Rounded2557‖ ≤ neighborMidpointP020Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP020Factor2557
      neighborMidpointP020Center2557)
  rw [neighborMidpointP020RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP020Factor2557 * embedPair2542 neighborMidpointP020Center2557)
    (embedPair2542 neighborMidpointP020Rounded2557)).trans (add_le_add
        neighborMidpointP020DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP020Factor2557, neighborMidpointP020Error2557,
      rounding2542,
      neighborMidpointP020Radius2557]

theorem neighborMidpointP020DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP020Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP020RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP020Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP020Radius2557, pairMagnitude2542, neighborMidpointP020Rounded2557]

def neighborMidpointP021Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP021Radius2557 : ℝ := ((1099663137061 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem neighborMidpointP021RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP021Factor2557 neighborMidpointP021Center2557) =
        neighborMidpointP021Rounded2557 := by
  cbv

theorem neighborMidpointP021RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP021Rounded2557‖ ≤ neighborMidpointP021Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP021Factor2557
      neighborMidpointP021Center2557)
  rw [neighborMidpointP021RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP021Factor2557 * embedPair2542 neighborMidpointP021Center2557)
    (embedPair2542 neighborMidpointP021Rounded2557)).trans (add_le_add
        neighborMidpointP021DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP021Factor2557, neighborMidpointP021Error2557,
      rounding2542,
      neighborMidpointP021Radius2557]

theorem neighborMidpointP021DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP021Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP021RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP021Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP021Radius2557, pairMagnitude2542, neighborMidpointP021Rounded2557]

def neighborMidpointP022Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP022Radius2557 : ℝ := ((1099663137097 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem neighborMidpointP022RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP022Factor2557 neighborMidpointP022Center2557) =
        neighborMidpointP022Rounded2557 := by
  cbv

theorem neighborMidpointP022RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP022Rounded2557‖ ≤ neighborMidpointP022Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP022Factor2557
      neighborMidpointP022Center2557)
  rw [neighborMidpointP022RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP022Factor2557 * embedPair2542 neighborMidpointP022Center2557)
    (embedPair2542 neighborMidpointP022Rounded2557)).trans (add_le_add
        neighborMidpointP022DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP022Factor2557, neighborMidpointP022Error2557,
      rounding2542,
      neighborMidpointP022Radius2557]

theorem neighborMidpointP022DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP022Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP022RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP022Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP022Radius2557, pairMagnitude2542, neighborMidpointP022Rounded2557]

def neighborMidpointP023Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP023Radius2557 : ℝ := ((68728946075 : ℝ) /
        (4 * 10^40
        + 3556142965880123323311949751266331066368))

theorem neighborMidpointP023RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP023Factor2557 neighborMidpointP023Center2557) =
        neighborMidpointP023Rounded2557 := by
  cbv

theorem neighborMidpointP023RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP023Rounded2557‖ ≤ neighborMidpointP023Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP023Factor2557
      neighborMidpointP023Center2557)
  rw [neighborMidpointP023RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP023Factor2557 * embedPair2542 neighborMidpointP023Center2557)
    (embedPair2542 neighborMidpointP023Rounded2557)).trans (add_le_add
        neighborMidpointP023DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP023Factor2557, neighborMidpointP023Error2557,
      rounding2542,
      neighborMidpointP023Radius2557]

theorem neighborMidpointP023DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP023Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP023RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP023Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP023Radius2557, pairMagnitude2542, neighborMidpointP023Rounded2557]

def neighborMidpointP024Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP024Radius2557 : ℝ := ((1099663137247 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem neighborMidpointP024RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP024Factor2557 neighborMidpointP024Center2557) =
        neighborMidpointP024Rounded2557 := by
  cbv

theorem neighborMidpointP024RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP024Rounded2557‖ ≤ neighborMidpointP024Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP024Factor2557
      neighborMidpointP024Center2557)
  rw [neighborMidpointP024RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP024Factor2557 * embedPair2542 neighborMidpointP024Center2557)
    (embedPair2542 neighborMidpointP024Rounded2557)).trans (add_le_add
        neighborMidpointP024DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP024Factor2557, neighborMidpointP024Error2557,
      rounding2542,
      neighborMidpointP024Radius2557]

theorem neighborMidpointP024DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP024Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP024RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP024Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP024Radius2557, pairMagnitude2542, neighborMidpointP024Rounded2557]

def neighborMidpointP025Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP025Radius2557 : ℝ := ((2199326274613 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem neighborMidpointP025RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP025Factor2557 neighborMidpointP025Center2557) =
        neighborMidpointP025Rounded2557 := by
  cbv

theorem neighborMidpointP025RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP025Rounded2557‖ ≤ neighborMidpointP025Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP025Factor2557
      neighborMidpointP025Center2557)
  rw [neighborMidpointP025RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP025Factor2557 * embedPair2542 neighborMidpointP025Center2557)
    (embedPair2542 neighborMidpointP025Rounded2557)).trans (add_le_add
        neighborMidpointP025DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP025Factor2557, neighborMidpointP025Error2557,
      rounding2542,
      neighborMidpointP025Radius2557]

theorem neighborMidpointP025DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP025Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP025RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP025Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP025Radius2557, pairMagnitude2542, neighborMidpointP025Rounded2557]

def neighborMidpointP026Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP026Radius2557 : ℝ := ((1099663137367 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem neighborMidpointP026RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP026Factor2557 neighborMidpointP026Center2557) =
        neighborMidpointP026Rounded2557 := by
  cbv

theorem neighborMidpointP026RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP026Rounded2557‖ ≤ neighborMidpointP026Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP026Factor2557
      neighborMidpointP026Center2557)
  rw [neighborMidpointP026RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP026Factor2557 * embedPair2542 neighborMidpointP026Center2557)
    (embedPair2542 neighborMidpointP026Rounded2557)).trans (add_le_add
        neighborMidpointP026DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP026Factor2557, neighborMidpointP026Error2557,
      rounding2542,
      neighborMidpointP026Radius2557]

theorem neighborMidpointP026DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP026Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP026RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP026Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP026Radius2557, pairMagnitude2542, neighborMidpointP026Rounded2557]

def neighborMidpointP027Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP027Radius2557 : ℝ := ((2199326274909 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem neighborMidpointP027RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP027Factor2557 neighborMidpointP027Center2557) =
        neighborMidpointP027Rounded2557 := by
  cbv

theorem neighborMidpointP027RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP027Rounded2557‖ ≤ neighborMidpointP027Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP027Factor2557
      neighborMidpointP027Center2557)
  rw [neighborMidpointP027RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP027Factor2557 * embedPair2542 neighborMidpointP027Center2557)
    (embedPair2542 neighborMidpointP027Rounded2557)).trans (add_le_add
        neighborMidpointP027DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP027Factor2557, neighborMidpointP027Error2557,
      rounding2542,
      neighborMidpointP027Radius2557]

theorem neighborMidpointP027DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP027Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP027RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP027Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP027Radius2557, pairMagnitude2542, neighborMidpointP027Rounded2557]

def neighborMidpointP028Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP028Radius2557 : ℝ := ((1099663137489 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem neighborMidpointP028RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP028Factor2557 neighborMidpointP028Center2557) =
        neighborMidpointP028Rounded2557 := by
  cbv

theorem neighborMidpointP028RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP028Rounded2557‖ ≤ neighborMidpointP028Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP028Factor2557
      neighborMidpointP028Center2557)
  rw [neighborMidpointP028RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP028Factor2557 * embedPair2542 neighborMidpointP028Center2557)
    (embedPair2542 neighborMidpointP028Rounded2557)).trans (add_le_add
        neighborMidpointP028DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP028Factor2557, neighborMidpointP028Error2557,
      rounding2542,
      neighborMidpointP028Radius2557]

theorem neighborMidpointP028DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP028Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP028RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP028Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP028Radius2557, pairMagnitude2542, neighborMidpointP028Rounded2557]

def neighborMidpointP029Rounded2557 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def neighborMidpointP029Radius2557 : ℝ := ((549831568771 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem neighborMidpointP029RoundCompute2557 :
    pairRound2542 (pairMul2542 neighborMidpointP029Factor2557 neighborMidpointP029Center2557) =
        neighborMidpointP029Rounded2557 := by
  cbv

theorem neighborMidpointP029RoundedError2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩ neighborMidpointPosition2557 -
      embedPair2542 neighborMidpointP029Rounded2557‖ ≤ neighborMidpointP029Radius2557 := by
  have hr := embedPair_round_error2542 (pairMul2542 neighborMidpointP029Factor2557
      neighborMidpointP029Center2557)
  rw [neighborMidpointP029RoundCompute2557, embedPair_mul2542] at hr
  have h := (neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP029Factor2557 * embedPair2542 neighborMidpointP029Center2557)
    (embedPair2542 neighborMidpointP029Rounded2557)).trans (add_le_add
        neighborMidpointP029DerivativeError2557 hr)
  apply h.trans
  norm_num [pairMagnitude2542, neighborMidpointP029Factor2557, neighborMidpointP029Error2557,
      rounding2542,
      neighborMidpointP029Radius2557]

theorem neighborMidpointP029DerivativeNorm2557 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩ neighborMidpointPosition2557‖ ≤
        1 := by
  have h := neighborMidpoint_triangle2557
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩ neighborMidpointPosition2557)
    (embedPair2542 neighborMidpointP029Rounded2557) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add neighborMidpointP029RoundedError2557 (embedPair_magnitude2542
      neighborMidpointP029Rounded2557))
  apply h'.trans
  norm_num [neighborMidpointP029Radius2557, pairMagnitude2542, neighborMidpointP029Rounded2557]

noncomputable def neighborSignedMidpointValue2557 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 neighborMidpointP000Rounded2557
  | 1 => embedPair2542 neighborMidpointP001Rounded2557
  | 2 => embedPair2542 neighborMidpointP002Rounded2557
  | 3 => embedPair2542 neighborMidpointP003Rounded2557
  | 4 => embedPair2542 neighborMidpointP004Rounded2557
  | 5 => embedPair2542 neighborMidpointP005Rounded2557
  | 6 => embedPair2542 neighborMidpointP006Rounded2557
  | 7 => embedPair2542 neighborMidpointP007Rounded2557
  | 8 => embedPair2542 neighborMidpointP008Rounded2557
  | 9 => embedPair2542 neighborMidpointP009Rounded2557
  | 10 => embedPair2542 neighborMidpointP010Rounded2557
  | 11 => embedPair2542 neighborMidpointP011Rounded2557
  | 12 => embedPair2542 neighborMidpointP012Rounded2557
  | 13 => embedPair2542 neighborMidpointP013Rounded2557
  | 14 => embedPair2542 neighborMidpointP014Rounded2557
  | 15 => embedPair2542 neighborMidpointP015Rounded2557
  | 16 => embedPair2542 neighborMidpointP016Rounded2557
  | 17 => embedPair2542 neighborMidpointP017Rounded2557
  | 18 => embedPair2542 neighborMidpointP018Rounded2557
  | 19 => embedPair2542 neighborMidpointP019Rounded2557
  | 20 => embedPair2542 neighborMidpointP020Rounded2557
  | 21 => embedPair2542 neighborMidpointP021Rounded2557
  | 22 => embedPair2542 neighborMidpointP022Rounded2557
  | 23 => embedPair2542 neighborMidpointP023Rounded2557
  | 24 => embedPair2542 neighborMidpointP024Rounded2557
  | 25 => embedPair2542 neighborMidpointP025Rounded2557
  | 26 => embedPair2542 neighborMidpointP026Rounded2557
  | 27 => embedPair2542 neighborMidpointP027Rounded2557
  | 28 => embedPair2542 neighborMidpointP028Rounded2557
  | 29 => embedPair2542 neighborMidpointP029Rounded2557
  | _ => 0

noncomputable def neighborSignedMidpointError2557 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => neighborMidpointP000Radius2557
  | 1 => neighborMidpointP001Radius2557
  | 2 => neighborMidpointP002Radius2557
  | 3 => neighborMidpointP003Radius2557
  | 4 => neighborMidpointP004Radius2557
  | 5 => neighborMidpointP005Radius2557
  | 6 => neighborMidpointP006Radius2557
  | 7 => neighborMidpointP007Radius2557
  | 8 => neighborMidpointP008Radius2557
  | 9 => neighborMidpointP009Radius2557
  | 10 => neighborMidpointP010Radius2557
  | 11 => neighborMidpointP011Radius2557
  | 12 => neighborMidpointP012Radius2557
  | 13 => neighborMidpointP013Radius2557
  | 14 => neighborMidpointP014Radius2557
  | 15 => neighborMidpointP015Radius2557
  | 16 => neighborMidpointP016Radius2557
  | 17 => neighborMidpointP017Radius2557
  | 18 => neighborMidpointP018Radius2557
  | 19 => neighborMidpointP019Radius2557
  | 20 => neighborMidpointP020Radius2557
  | 21 => neighborMidpointP021Radius2557
  | 22 => neighborMidpointP022Radius2557
  | 23 => neighborMidpointP023Radius2557
  | 24 => neighborMidpointP024Radius2557
  | 25 => neighborMidpointP025Radius2557
  | 26 => neighborMidpointP026Radius2557
  | 27 => neighborMidpointP027Radius2557
  | 28 => neighborMidpointP028Radius2557
  | 29 => neighborMidpointP029Radius2557
  | _ => 0

theorem neighborSignedMidpointExpError2557 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i neighborMidpointPosition2557 -
        neighborSignedMidpointValue2557 i‖ ≤ neighborSignedMidpointError2557 i := by
  fin_cases i
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP000RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP001RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP002RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP003RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP004RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP005RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP006RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP007RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP008RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP009RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP010RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP011RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP012RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP013RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP014RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP015RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP016RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP017RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP018RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP019RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP020RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP021RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP022RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP023RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP024RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP025RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP026RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP027RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP028RoundedError2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP029RoundedError2557

theorem neighborSignedMidpointUnitNorm2557 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i neighborMidpointPosition2557‖ ≤ 1 := by
  fin_cases i
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP000DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP001DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP002DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP003DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP004DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP005DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP006DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP007DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP008DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP009DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP010DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP011DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP012DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP013DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP014DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP015DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP016DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP017DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP018DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP019DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP020DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP021DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP022DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP023DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP024DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP025DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP026DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP027DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP028DerivativeNorm2557
  · simpa only [neighborSignedMidpointValue2557, neighborSignedMidpointError2557] using
      neighborMidpointP029DerivativeNorm2557

noncomputable def neighborSignedMidpointSum2557 : ℂ := ⟨(((-(((947 * 10^40
        + 4148927455672866281683445464612374186451) * 10^40
        + 9869518112093822604342230660938179157173) * 10^40
        + 9442048936526063369057414461037367943599)) : ℝ) /
        (((5415370 * 10^40
        + 4963297165226140902034044603582742911628) * 10^40
        + 4339174837984293088793224180786254499995) * 10^40
        + 11922147613471467208908991351228465152)),
    (((-(((318 * 10^40
        + 2013500344584199615243726036303870806886) * 10^40
        + 6217380187075847823382740464814694168960) * 10^40
        + 5329538495615481630046101125485111248029)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216))⟩

noncomputable def neighborSignedMidpointUpper2557 : ℝ := ((17521 : ℝ) /
        100000000)

theorem neighborSignedMidpointSum_eq2557 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * neighborSignedMidpointValue2557 i) =
      neighborSignedMidpointSum2557 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, neighborSignedMidpointValue2557,
      neighborSignedMidpointSum2557, embedPair2542, neighborMidpointP000Rounded2557,
      neighborMidpointP001Rounded2557,
      neighborMidpointP002Rounded2557,
      neighborMidpointP003Rounded2557,
      neighborMidpointP004Rounded2557,
      neighborMidpointP005Rounded2557,
      neighborMidpointP006Rounded2557,
      neighborMidpointP007Rounded2557,
      neighborMidpointP008Rounded2557,
      neighborMidpointP009Rounded2557,
      neighborMidpointP010Rounded2557,
      neighborMidpointP011Rounded2557,
      neighborMidpointP012Rounded2557,
      neighborMidpointP013Rounded2557,
      neighborMidpointP014Rounded2557,
      neighborMidpointP015Rounded2557,
      neighborMidpointP016Rounded2557,
      neighborMidpointP017Rounded2557,
      neighborMidpointP018Rounded2557,
      neighborMidpointP019Rounded2557,
      neighborMidpointP020Rounded2557,
      neighborMidpointP021Rounded2557,
      neighborMidpointP022Rounded2557,
      neighborMidpointP023Rounded2557,
      neighborMidpointP024Rounded2557,
      neighborMidpointP025Rounded2557,
      neighborMidpointP026Rounded2557,
      neighborMidpointP027Rounded2557,
      neighborMidpointP028Rounded2557,
      neighborMidpointP029Rounded2557, Complex.mul_re, Complex.mul_im]

theorem neighborSignedMidpointSum_norm2557 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * neighborSignedMidpointValue2557 i‖ ≤ ((17511 : ℝ)
        /
        100000000) := by
  rw [neighborSignedMidpointSum_eq2557]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [neighborSignedMidpointSum2557]

theorem neighborSignedMidpointCharge2557 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * neighborSignedMidpointError2557 i) ≤ (1 : ℝ)/10^8 :=
          by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, neighborSignedMidpointError2557,
      neighborMidpointP000Radius2557,
      neighborMidpointP001Radius2557,
      neighborMidpointP002Radius2557,
      neighborMidpointP003Radius2557,
      neighborMidpointP004Radius2557,
      neighborMidpointP005Radius2557,
      neighborMidpointP006Radius2557,
      neighborMidpointP007Radius2557,
      neighborMidpointP008Radius2557,
      neighborMidpointP009Radius2557,
      neighborMidpointP010Radius2557,
      neighborMidpointP011Radius2557,
      neighborMidpointP012Radius2557,
      neighborMidpointP013Radius2557,
      neighborMidpointP014Radius2557,
      neighborMidpointP015Radius2557,
      neighborMidpointP016Radius2557,
      neighborMidpointP017Radius2557,
      neighborMidpointP018Radius2557,
      neighborMidpointP019Radius2557,
      neighborMidpointP020Radius2557,
      neighborMidpointP021Radius2557,
      neighborMidpointP022Radius2557,
      neighborMidpointP023Radius2557,
      neighborMidpointP024Radius2557,
      neighborMidpointP025Radius2557,
      neighborMidpointP026Radius2557,
      neighborMidpointP027Radius2557,
      neighborMidpointP028Radius2557,
      neighborMidpointP029Radius2557]

theorem neighborSignedMidpointUpper_le2557 :
    signedJetUpper2539 2 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 neighborMidpointPosition2557 ≤ neighborSignedMidpointUpper2557 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i neighborMidpointPosition2557‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * neighborSignedMidpointValue2557 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * neighborSignedMidpointError2557 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (neighborSignedMidpointExpError2557 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i neighborMidpointPosition2557‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (neighborSignedMidpointUnitNorm2557 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i neighborMidpointPosition2557‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 neighborSignedMidpointUpper2557
  linarith [neighborSignedMidpointSum_norm2557, neighborSignedMidpointCharge2557]

theorem neighborPhysicalSecond2557 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        neighborMidpointPosition2557‖ ≤
      neighborSignedMidpointUpper2557 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        neighborMidpointPosition2557
  exact h.trans neighborSignedMidpointUpper_le2557

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.neighborSignedMidpointExpError2557
#print axioms ConnesWeilRH.Dev.neighborSignedMidpointSum_eq2557
#print axioms ConnesWeilRH.Dev.neighborSignedMidpointCharge2557
#print axioms ConnesWeilRH.Dev.neighborSignedMidpointUpper_le2557
#print axioms ConnesWeilRH.Dev.neighborPhysicalSecond2557
