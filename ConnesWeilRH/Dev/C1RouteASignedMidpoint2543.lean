import ConnesWeilRH.Dev.C1RouteAMidpointDerivatives2543

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem midpoint_triangle2543 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def midpointP000Rounded2543 : RatPair2542 :=
  (((21738106001276688775 : ℚ) /
        316912650057057350374175801344),
    (((-55663944215352541147) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP000Radius2543 : ℝ := ((72281461817966181 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem midpointP000RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP000Factor2543 midpointP000Center2543) =
        midpointP000Rounded2543 := by
  cbv

theorem midpointP000RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP000Rounded2543‖ ≤ midpointP000Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP000Factor2543 midpointP000Center2543)
  rw [midpointP000RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP000Factor2543 * embedPair2542 midpointP000Center2543)
    (embedPair2542 midpointP000Rounded2543)).trans (add_le_add midpointP000DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP000Factor2543, midpointP000Error2543, rounding2542,
      midpointP000Radius2543]

theorem midpointP000DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP000Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP000RoundedError2543 (embedPair_magnitude2542
      midpointP000Rounded2543))
  apply h'.trans
  norm_num [midpointP000Radius2543, pairMagnitude2542, midpointP000Rounded2543]

def midpointP001Rounded2543 : RatPair2542 :=
  (((63934752890799114727 : ℚ) /
        633825300114114700748351602688),
    (((-66864770410108281027) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP001Radius2543 : ℝ := ((5778304102818565 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem midpointP001RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP001Factor2543 midpointP001Center2543) =
        midpointP001Rounded2543 := by
  cbv

theorem midpointP001RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP001Rounded2543‖ ≤ midpointP001Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP001Factor2543 midpointP001Center2543)
  rw [midpointP001RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP001Factor2543 * embedPair2542 midpointP001Center2543)
    (embedPair2542 midpointP001Rounded2543)).trans (add_le_add midpointP001DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP001Factor2543, midpointP001Error2543, rounding2542,
      midpointP001Radius2543]

theorem midpointP001DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP001Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP001RoundedError2543 (embedPair_magnitude2542
      midpointP001Rounded2543))
  apply h'.trans
  norm_num [midpointP001Radius2543, pairMagnitude2542, midpointP001Rounded2543]

def midpointP002Rounded2543 : RatPair2542 :=
  (((1212628967382368591 : ℚ) /
        9903520314283042199192993792),
    ((18155077305405928009 : ℚ) /
        316912650057057350374175801344))

noncomputable def midpointP002Radius2543 : ℝ := ((104661153456093919 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem midpointP002RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP002Factor2543 midpointP002Center2543) =
        midpointP002Rounded2543 := by
  cbv

theorem midpointP002RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP002Rounded2543‖ ≤ midpointP002Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP002Factor2543 midpointP002Center2543)
  rw [midpointP002RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP002Factor2543 * embedPair2542 midpointP002Center2543)
    (embedPair2542 midpointP002Rounded2543)).trans (add_le_add midpointP002DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP002Factor2543, midpointP002Error2543, rounding2542,
      midpointP002Radius2543]

theorem midpointP002DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP002Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP002RoundedError2543 (embedPair_magnitude2542
      midpointP002Rounded2543))
  apply h'.trans
  norm_num [midpointP002Radius2543, pairMagnitude2542, midpointP002Rounded2543]

def midpointP003Rounded2543 : RatPair2542 :=
  (((86351424942667326663 : ℚ) /
        633825300114114700748351602688),
    ((75731973038887865233 : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP003Radius2543 : ℝ := ((14006106795511087 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem midpointP003RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP003Factor2543 midpointP003Center2543) =
        midpointP003Rounded2543 := by
  cbv

theorem midpointP003RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP003Rounded2543‖ ≤ midpointP003Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP003Factor2543 midpointP003Center2543)
  rw [midpointP003RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP003Factor2543 * embedPair2542 midpointP003Center2543)
    (embedPair2542 midpointP003Rounded2543)).trans (add_le_add midpointP003DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP003Factor2543, midpointP003Error2543, rounding2542,
      midpointP003Radius2543]

theorem midpointP003DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP003Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP003RoundedError2543 (embedPair_magnitude2542
      midpointP003Rounded2543))
  apply h'.trans
  norm_num [midpointP003Radius2543, pairMagnitude2542, midpointP003Rounded2543]

def midpointP004Rounded2543 : RatPair2542 :=
  (((183916036350257027153 : ℚ) /
        1267650600228229401496703205376),
    (((-77522810836922734383) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP004Radius2543 : ℝ := ((116635693169344685 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem midpointP004RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP004Factor2543 midpointP004Center2543) =
        midpointP004Rounded2543 := by
  cbv

theorem midpointP004RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP004Rounded2543‖ ≤ midpointP004Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP004Factor2543 midpointP004Center2543)
  rw [midpointP004RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP004Factor2543 * embedPair2542 midpointP004Center2543)
    (embedPair2542 midpointP004Rounded2543)).trans (add_le_add midpointP004DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP004Factor2543, midpointP004Error2543, rounding2542,
      midpointP004Radius2543]

theorem midpointP004DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP004Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP004RoundedError2543 (embedPair_magnitude2542
      midpointP004Rounded2543))
  apply h'.trans
  norm_num [midpointP004Radius2543, pairMagnitude2542, midpointP004Rounded2543]

def midpointP005Rounded2543 : RatPair2542 :=
  ((((-42487894600732975) : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def midpointP005Radius2543 : ℝ := ((6195920416527 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem midpointP005RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP005Factor2543 midpointP005Center2543) =
        midpointP005Rounded2543 := by
  cbv

theorem midpointP005RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP005Rounded2543‖ ≤ midpointP005Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP005Factor2543 midpointP005Center2543)
  rw [midpointP005RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP005Factor2543 * embedPair2542 midpointP005Center2543)
    (embedPair2542 midpointP005Rounded2543)).trans (add_le_add midpointP005DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP005Factor2543, midpointP005Error2543, rounding2542,
      midpointP005Radius2543]

theorem midpointP005DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP005Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP005RoundedError2543 (embedPair_magnitude2542
      midpointP005Rounded2543))
  apply h'.trans
  norm_num [midpointP005Radius2543, pairMagnitude2542, midpointP005Rounded2543]

def midpointP006Rounded2543 : RatPair2542 :=
  ((((-301220989100721649) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def midpointP006Radius2543 : ℝ := ((17808053841391 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem midpointP006RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP006Factor2543 midpointP006Center2543) =
        midpointP006Rounded2543 := by
  cbv

theorem midpointP006RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP006Rounded2543‖ ≤ midpointP006Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP006Factor2543 midpointP006Center2543)
  rw [midpointP006RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP006Factor2543 * embedPair2542 midpointP006Center2543)
    (embedPair2542 midpointP006Rounded2543)).trans (add_le_add midpointP006DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP006Factor2543, midpointP006Error2543, rounding2542,
      midpointP006Radius2543]

theorem midpointP006DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP006Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP006RoundedError2543 (embedPair_magnitude2542
      midpointP006Rounded2543))
  apply h'.trans
  norm_num [midpointP006Radius2543, pairMagnitude2542, midpointP006Rounded2543]

def midpointP007Rounded2543 : RatPair2542 :=
  ((((-246262167212844697) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def midpointP007Radius2543 : ℝ := ((1795955351067 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem midpointP007RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP007Factor2543 midpointP007Center2543) =
        midpointP007Rounded2543 := by
  cbv

theorem midpointP007RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP007Rounded2543‖ ≤ midpointP007Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP007Factor2543 midpointP007Center2543)
  rw [midpointP007RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP007Factor2543 * embedPair2542 midpointP007Center2543)
    (embedPair2542 midpointP007Rounded2543)).trans (add_le_add midpointP007DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP007Factor2543, midpointP007Error2543, rounding2542,
      midpointP007Radius2543]

theorem midpointP007DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP007Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP007RoundedError2543 (embedPair_magnitude2542
      midpointP007Rounded2543))
  apply h'.trans
  norm_num [midpointP007Radius2543, pairMagnitude2542, midpointP007Rounded2543]

def midpointP008Rounded2543 : RatPair2542 :=
  ((((-17664044116677137493) : ℚ) /
        1267650600228229401496703205376),
    (((-1711383848498076283) : ℚ) /
        633825300114114700748351602688))

noncomputable def midpointP008Radius2543 : ℝ := ((1055704364293867 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem midpointP008RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP008Factor2543 midpointP008Center2543) =
        midpointP008Rounded2543 := by
  cbv

theorem midpointP008RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP008Rounded2543‖ ≤ midpointP008Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP008Factor2543 midpointP008Center2543)
  rw [midpointP008RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP008Factor2543 * embedPair2542 midpointP008Center2543)
    (embedPair2542 midpointP008Rounded2543)).trans (add_le_add midpointP008DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP008Factor2543, midpointP008Error2543, rounding2542,
      midpointP008Radius2543]

theorem midpointP008DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP008Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP008RoundedError2543 (embedPair_magnitude2542
      midpointP008Rounded2543))
  apply h'.trans
  norm_num [midpointP008Radius2543, pairMagnitude2542, midpointP008Rounded2543]

def midpointP009Rounded2543 : RatPair2542 :=
  (((31912648949149399069 : ℚ) /
        1267650600228229401496703205376),
    ((21797091296641492141 : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP009Radius2543 : ℝ := ((25247291290233307 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem midpointP009RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP009Factor2543 midpointP009Center2543) =
        midpointP009Rounded2543 := by
  cbv

theorem midpointP009RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP009Rounded2543‖ ≤ midpointP009Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP009Factor2543 midpointP009Center2543)
  rw [midpointP009RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP009Factor2543 * embedPair2542 midpointP009Center2543)
    (embedPair2542 midpointP009Rounded2543)).trans (add_le_add midpointP009DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP009Factor2543, midpointP009Error2543, rounding2542,
      midpointP009Radius2543]

theorem midpointP009DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP009Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP009RoundedError2543 (embedPair_magnitude2542
      midpointP009Rounded2543))
  apply h'.trans
  norm_num [midpointP009Radius2543, pairMagnitude2542, midpointP009Rounded2543]

def midpointP010Rounded2543 : RatPair2542 :=
  (((7266944204805004767 : ℚ) /
        316912650057057350374175801344),
    (((-22933001658140955691) : ℚ) /
        633825300114114700748351602688))

noncomputable def midpointP010Radius2543 : ℝ := ((2141554464794457 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem midpointP010RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP010Factor2543 midpointP010Center2543) =
        midpointP010Rounded2543 := by
  cbv

theorem midpointP010RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP010Rounded2543‖ ≤ midpointP010Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP010Factor2543 midpointP010Center2543)
  rw [midpointP010RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP010Factor2543 * embedPair2542 midpointP010Center2543)
    (embedPair2542 midpointP010Rounded2543)).trans (add_le_add midpointP010DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP010Factor2543, midpointP010Error2543, rounding2542,
      midpointP010Radius2543]

theorem midpointP010DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP010Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP010RoundedError2543 (embedPair_magnitude2542
      midpointP010Rounded2543))
  apply h'.trans
  norm_num [midpointP010Radius2543, pairMagnitude2542, midpointP010Rounded2543]

def midpointP011Rounded2543 : RatPair2542 :=
  ((((-32348580984032803639) : ℚ) /
        1267650600228229401496703205376),
    (((-28905040982601475661) : ℚ) /
        633825300114114700748351602688))

noncomputable def midpointP011Radius2543 : ℝ := ((9427184707586909 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem midpointP011RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP011Factor2543 midpointP011Center2543) =
        midpointP011Rounded2543 := by
  cbv

theorem midpointP011RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP011Rounded2543‖ ≤ midpointP011Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP011Factor2543 midpointP011Center2543)
  rw [midpointP011RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP011Factor2543 * embedPair2542 midpointP011Center2543)
    (embedPair2542 midpointP011Rounded2543)).trans (add_le_add midpointP011DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP011Factor2543, midpointP011Error2543, rounding2542,
      midpointP011Radius2543]

theorem midpointP011DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP011Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP011RoundedError2543 (embedPair_magnitude2542
      midpointP011Rounded2543))
  apply h'.trans
  norm_num [midpointP011Radius2543, pairMagnitude2542, midpointP011Rounded2543]

def midpointP012Rounded2543 : RatPair2542 :=
  ((((-19940830133191685515) : ℚ) /
        316912650057057350374175801344),
    ((4446411287964550507 : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP012Radius2543 : ℝ := ((26112398701878481 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem midpointP012RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP012Factor2543 midpointP012Center2543) =
        midpointP012Rounded2543 := by
  cbv

theorem midpointP012RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP012Rounded2543‖ ≤ midpointP012Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP012Factor2543 midpointP012Center2543)
  rw [midpointP012RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP012Factor2543 * embedPair2542 midpointP012Center2543)
    (embedPair2542 midpointP012Rounded2543)).trans (add_le_add midpointP012DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP012Factor2543, midpointP012Error2543, rounding2542,
      midpointP012Radius2543]

theorem midpointP012DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP012Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP012RoundedError2543 (embedPair_magnitude2542
      midpointP012Rounded2543))
  apply h'.trans
  norm_num [midpointP012Radius2543, pairMagnitude2542, midpointP012Rounded2543]

def midpointP013Rounded2543 : RatPair2542 :=
  ((((-11115251792142198915) : ℚ) /
        316912650057057350374175801344),
    ((41094998902721692721 : ℚ) /
        633825300114114700748351602688))

noncomputable def midpointP013Radius2543 : ℝ := ((50019883465347157 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem midpointP013RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP013Factor2543 midpointP013Center2543) =
        midpointP013Rounded2543 := by
  cbv

theorem midpointP013RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP013Rounded2543‖ ≤ midpointP013Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP013Factor2543 midpointP013Center2543)
  rw [midpointP013RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP013Factor2543 * embedPair2542 midpointP013Center2543)
    (embedPair2542 midpointP013Rounded2543)).trans (add_le_add midpointP013DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP013Factor2543, midpointP013Error2543, rounding2542,
      midpointP013Radius2543]

theorem midpointP013DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP013Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP013RoundedError2543 (embedPair_magnitude2542
      midpointP013Rounded2543))
  apply h'.trans
  norm_num [midpointP013Radius2543, pairMagnitude2542, midpointP013Rounded2543]

def midpointP014Rounded2543 : RatPair2542 :=
  (((59780959804673221683 : ℚ) /
        633825300114114700748351602688),
    ((21075284559485159787 : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP014Radius2543 : ℝ := ((37235299683123589 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem midpointP014RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP014Factor2543 midpointP014Center2543) =
        midpointP014Rounded2543 := by
  cbv

theorem midpointP014RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP014Rounded2543‖ ≤ midpointP014Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP014Factor2543 midpointP014Center2543)
  rw [midpointP014RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP014Factor2543 * embedPair2542 midpointP014Center2543)
    (embedPair2542 midpointP014Rounded2543)).trans (add_le_add midpointP014DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP014Factor2543, midpointP014Error2543, rounding2542,
      midpointP014Radius2543]

theorem midpointP014DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP014Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP014RoundedError2543 (embedPair_magnitude2542
      midpointP014Rounded2543))
  apply h'.trans
  norm_num [midpointP014Radius2543, pairMagnitude2542, midpointP014Rounded2543]

def midpointP015Rounded2543 : RatPair2542 :=
  (((13570142705041053033 : ℚ) /
        316912650057057350374175801344),
    (((-133060682736279359907) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP015Radius2543 : ℝ := ((13550840177562403 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem midpointP015RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP015Factor2543 midpointP015Center2543) =
        midpointP015Rounded2543 := by
  cbv

theorem midpointP015RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP015Rounded2543‖ ≤ midpointP015Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP015Factor2543 midpointP015Center2543)
  rw [midpointP015RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP015Factor2543 * embedPair2542 midpointP015Center2543)
    (embedPair2542 midpointP015Rounded2543)).trans (add_le_add midpointP015DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP015Factor2543, midpointP015Error2543, rounding2542,
      midpointP015Radius2543]

theorem midpointP015DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP015Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP015RoundedError2543 (embedPair_magnitude2542
      midpointP015Rounded2543))
  apply h'.trans
  norm_num [midpointP015Radius2543, pairMagnitude2542, midpointP015Rounded2543]

def midpointP016Rounded2543 : RatPair2542 :=
  ((((-90228470303487116287) : ℚ) /
        1267650600228229401496703205376),
    (((-66671365068117345387) : ℚ) /
        633825300114114700748351602688))

noncomputable def midpointP016Radius2543 : ℝ := ((55905604153329585 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem midpointP016RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP016Factor2543 midpointP016Center2543) =
        midpointP016Rounded2543 := by
  cbv

theorem midpointP016RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP016Rounded2543‖ ≤ midpointP016Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP016Factor2543 midpointP016Center2543)
  rw [midpointP016RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP016Factor2543 * embedPair2542 midpointP016Center2543)
    (embedPair2542 midpointP016Rounded2543)).trans (add_le_add midpointP016DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP016Factor2543, midpointP016Error2543, rounding2542,
      midpointP016Radius2543]

theorem midpointP016DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP016Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP016RoundedError2543 (embedPair_magnitude2542
      midpointP016Rounded2543))
  apply h'.trans
  norm_num [midpointP016Radius2543, pairMagnitude2542, midpointP016Rounded2543]

def midpointP017Rounded2543 : RatPair2542 :=
  ((((-117447979250910804411) : ℚ) /
        1267650600228229401496703205376),
    ((4958939348191902533 : ℚ) /
        39614081257132168796771975168))

noncomputable def midpointP017Radius2543 : ℝ := ((62481575288819527 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem midpointP017RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP017Factor2543 midpointP017Center2543) =
        midpointP017Rounded2543 := by
  cbv

theorem midpointP017RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP017Rounded2543‖ ≤ midpointP017Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP017Factor2543 midpointP017Center2543)
  rw [midpointP017RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP017Factor2543 * embedPair2542 midpointP017Center2543)
    (embedPair2542 midpointP017Rounded2543)).trans (add_le_add midpointP017DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP017Factor2543, midpointP017Error2543, rounding2542,
      midpointP017Radius2543]

theorem midpointP017DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP017Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP017RoundedError2543 (embedPair_magnitude2542
      midpointP017Rounded2543))
  apply h'.trans
  norm_num [midpointP017Radius2543, pairMagnitude2542, midpointP017Rounded2543]

def midpointP018Rounded2543 : RatPair2542 :=
  (((2258664761930552815 : ℚ) /
        158456325028528675187087900672),
    ((211392345679003375047 : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP018Radius2543 : ℝ := ((76281245839027535 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem midpointP018RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP018Factor2543 midpointP018Center2543) =
        midpointP018Rounded2543 := by
  cbv

theorem midpointP018RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP018Rounded2543‖ ≤ midpointP018Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP018Factor2543 midpointP018Center2543)
  rw [midpointP018RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP018Factor2543 * embedPair2542 midpointP018Center2543)
    (embedPair2542 midpointP018Rounded2543)).trans (add_le_add midpointP018DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP018Factor2543, midpointP018Error2543, rounding2542,
      midpointP018Radius2543]

theorem midpointP018DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP018Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP018RoundedError2543 (embedPair_magnitude2542
      midpointP018Rounded2543))
  apply h'.trans
  norm_num [midpointP018Radius2543, pairMagnitude2542, midpointP018Rounded2543]

def midpointP019Rounded2543 : RatPair2542 :=
  (((236304621205900107923 : ℚ) /
        1267650600228229401496703205376),
    ((21424456151709639659 : ℚ) /
        633825300114114700748351602688))

noncomputable def midpointP019Radius2543 : ℝ := ((137370649613911949 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem midpointP019RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP019Factor2543 midpointP019Center2543) =
        midpointP019Rounded2543 := by
  cbv

theorem midpointP019RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP019Rounded2543‖ ≤ midpointP019Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP019Factor2543 midpointP019Center2543)
  rw [midpointP019RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP019Factor2543 * embedPair2542 midpointP019Center2543)
    (embedPair2542 midpointP019Rounded2543)).trans (add_le_add midpointP019DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP019Factor2543, midpointP019Error2543, rounding2542,
      midpointP019Radius2543]

theorem midpointP019DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP019Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP019RoundedError2543 (embedPair_magnitude2542
      midpointP019Rounded2543))
  apply h'.trans
  norm_num [midpointP019Radius2543, pairMagnitude2542, midpointP019Rounded2543]

def midpointP020Rounded2543 : RatPair2542 :=
  (((88116986320646281349 : ℚ) /
        1267650600228229401496703205376),
    (((-257941306741932703947) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP020Radius2543 : ℝ := ((80248056958733723 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem midpointP020RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP020Factor2543 midpointP020Center2543) =
        midpointP020Rounded2543 := by
  cbv

theorem midpointP020RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP020Rounded2543‖ ≤ midpointP020Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP020Factor2543 midpointP020Center2543)
  rw [midpointP020RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP020Factor2543 * embedPair2542 midpointP020Center2543)
    (embedPair2542 midpointP020Rounded2543)).trans (add_le_add midpointP020DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP020Factor2543, midpointP020Error2543, rounding2542,
      midpointP020Radius2543]

theorem midpointP020DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP020Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP020RoundedError2543 (embedPair_magnitude2542
      midpointP020Rounded2543))
  apply h'.trans
  norm_num [midpointP020Radius2543, pairMagnitude2542, midpointP020Rounded2543]

def midpointP021Rounded2543 : RatPair2542 :=
  ((((-227703451949503784747) : ℚ) /
        1267650600228229401496703205376),
    (((-197174893479346352601) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP021Radius2543 : ℝ := ((63083873144746583 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem midpointP021RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP021Factor2543 midpointP021Center2543) =
        midpointP021Rounded2543 := by
  cbv

theorem midpointP021RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP021Rounded2543‖ ≤ midpointP021Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP021Factor2543 midpointP021Center2543)
  rw [midpointP021RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP021Factor2543 * embedPair2542 midpointP021Center2543)
    (embedPair2542 midpointP021Rounded2543)).trans (add_le_add midpointP021DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP021Factor2543, midpointP021Error2543, rounding2542,
      midpointP021Radius2543]

theorem midpointP021DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP021Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP021RoundedError2543 (embedPair_magnitude2542
      midpointP021Rounded2543))
  apply h'.trans
  norm_num [midpointP021Radius2543, pairMagnitude2542, midpointP021Rounded2543]

def midpointP022Rounded2543 : RatPair2542 :=
  ((((-157315758717293228013) : ℚ) /
        633825300114114700748351602688),
    (((-524728587360346531) : ℚ) /
        19807040628566084398385987584))

noncomputable def midpointP022Radius2543 : ℝ := ((89010565153273 : ℝ) /
        1361129467683753853853498429727072845824)

theorem midpointP022RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP022Factor2543 midpointP022Center2543) =
        midpointP022Rounded2543 := by
  cbv

theorem midpointP022RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP022Rounded2543‖ ≤ midpointP022Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP022Factor2543 midpointP022Center2543)
  rw [midpointP022RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP022Factor2543 * embedPair2542 midpointP022Center2543)
    (embedPair2542 midpointP022Rounded2543)).trans (add_le_add midpointP022DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP022Factor2543, midpointP022Error2543, rounding2542,
      midpointP022Radius2543]

theorem midpointP022DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP022Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP022RoundedError2543 (embedPair_magnitude2542
      midpointP022Rounded2543))
  apply h'.trans
  norm_num [midpointP022Radius2543, pairMagnitude2542, midpointP022Rounded2543]

def midpointP023Rounded2543 : RatPair2542 :=
  (((26927570351116582615 : ℚ) /
        1267650600228229401496703205376),
    ((180686616397859478955 : ℚ) /
        633825300114114700748351602688))

noncomputable def midpointP023Radius2543 : ℝ := ((203241083897737847 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem midpointP023RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP023Factor2543 midpointP023Center2543) =
        midpointP023Rounded2543 := by
  cbv

theorem midpointP023RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP023Rounded2543‖ ≤ midpointP023Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP023Factor2543 midpointP023Center2543)
  rw [midpointP023RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP023Factor2543 * embedPair2542 midpointP023Center2543)
    (embedPair2542 midpointP023Rounded2543)).trans (add_le_add midpointP023DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP023Factor2543, midpointP023Error2543, rounding2542,
      midpointP023Radius2543]

theorem midpointP023DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP023Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP023RoundedError2543 (embedPair_magnitude2542
      midpointP023Rounded2543))
  apply h'.trans
  norm_num [midpointP023Radius2543, pairMagnitude2542, midpointP023Rounded2543]

def midpointP024Rounded2543 : RatPair2542 :=
  (((296258369598975014053 : ℚ) /
        1267650600228229401496703205376),
    ((245161019907676308947 : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP024Radius2543 : ℝ := ((231829006119207429 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem midpointP024RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP024Factor2543 midpointP024Center2543) =
        midpointP024Rounded2543 := by
  cbv

theorem midpointP024RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP024Rounded2543‖ ≤ midpointP024Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP024Factor2543 midpointP024Center2543)
  rw [midpointP024RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP024Factor2543 * embedPair2542 midpointP024Center2543)
    (embedPair2542 midpointP024Rounded2543)).trans (add_le_add midpointP024DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP024Factor2543, midpointP024Error2543, rounding2542,
      midpointP024Radius2543]

theorem midpointP024DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP024Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP024RoundedError2543 (embedPair_magnitude2542
      midpointP024Rounded2543))
  apply h'.trans
  norm_num [midpointP024Radius2543, pairMagnitude2542, midpointP024Rounded2543]

def midpointP025Rounded2543 : RatPair2542 :=
  (((196253214121160948919 : ℚ) /
        633825300114114700748351602688),
    (((-129343175223357519529) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP025Radius2543 : ℝ := ((60498814939435011 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem midpointP025RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP025Factor2543 midpointP025Center2543) =
        midpointP025Rounded2543 := by
  cbv

theorem midpointP025RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP025Rounded2543‖ ≤ midpointP025Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP025Factor2543 midpointP025Center2543)
  rw [midpointP025RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP025Factor2543 * embedPair2542 midpointP025Center2543)
    (embedPair2542 midpointP025Rounded2543)).trans (add_le_add midpointP025DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP025Factor2543, midpointP025Error2543, rounding2542,
      midpointP025Radius2543]

theorem midpointP025DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP025Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP025RoundedError2543 (embedPair_magnitude2542
      midpointP025Rounded2543))
  apply h'.trans
  norm_num [midpointP025Radius2543, pairMagnitude2542, midpointP025Rounded2543]

def midpointP026Rounded2543 : RatPair2542 :=
  (((97051250359648164387 : ℚ) /
        1267650600228229401496703205376),
    (((-432952905618537248291) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP026Radius2543 : ℝ := ((165193024805977659 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem midpointP026RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP026Factor2543 midpointP026Center2543) =
        midpointP026Rounded2543 := by
  cbv

theorem midpointP026RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP026Rounded2543‖ ≤ midpointP026Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP026Factor2543 midpointP026Center2543)
  rw [midpointP026RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP026Factor2543 * embedPair2542 midpointP026Center2543)
    (embedPair2542 midpointP026Rounded2543)).trans (add_le_add midpointP026DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP026Factor2543, midpointP026Error2543, rounding2542,
      midpointP026Radius2543]

theorem midpointP026DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP026Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP026RoundedError2543 (embedPair_magnitude2542
      midpointP026Rounded2543))
  apply h'.trans
  norm_num [midpointP026Radius2543, pairMagnitude2542, midpointP026Rounded2543]

def midpointP027Rounded2543 : RatPair2542 :=
  ((((-233687325883660470645) : ℚ) /
        633825300114114700748351602688),
    (((-145556917342315154279) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP027Radius2543 : ℝ := ((266299112732064767 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem midpointP027RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP027Factor2543 midpointP027Center2543) =
        midpointP027Rounded2543 := by
  cbv

theorem midpointP027RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP027Rounded2543‖ ≤ midpointP027Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP027Factor2543 midpointP027Center2543)
  rw [midpointP027RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP027Factor2543 * embedPair2542 midpointP027Center2543)
    (embedPair2542 midpointP027Rounded2543)).trans (add_le_add midpointP027DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP027Factor2543, midpointP027Error2543, rounding2542,
      midpointP027Radius2543]

theorem midpointP027DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP027Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP027RoundedError2543 (embedPair_magnitude2542
      midpointP027Rounded2543))
  apply h'.trans
  norm_num [midpointP027Radius2543, pairMagnitude2542, midpointP027Rounded2543]

def midpointP028Rounded2543 : RatPair2542 :=
  ((((-487369640813316342365) : ℚ) /
        1267650600228229401496703205376),
    ((36071954886596327213 : ℚ) /
        316912650057057350374175801344))

noncomputable def midpointP028Radius2543 : ℝ := ((261174721312192789 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem midpointP028RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP028Factor2543 midpointP028Center2543) =
        midpointP028Rounded2543 := by
  cbv

theorem midpointP028RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP028Rounded2543‖ ≤ midpointP028Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP028Factor2543 midpointP028Center2543)
  rw [midpointP028RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP028Factor2543 * embedPair2542 midpointP028Center2543)
    (embedPair2542 midpointP028Rounded2543)).trans (add_le_add midpointP028DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP028Factor2543, midpointP028Error2543, rounding2542,
      midpointP028Radius2543]

theorem midpointP028DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP028Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP028RoundedError2543 (embedPair_magnitude2542
      midpointP028Rounded2543))
  apply h'.trans
  norm_num [midpointP028Radius2543, pairMagnitude2542, midpointP028Rounded2543]

def midpointP029Rounded2543 : RatPair2542 :=
  ((((-201891037034814707581) : ℚ) /
        1267650600228229401496703205376),
    ((249084848588047606693 : ℚ) /
        633825300114114700748351602688))

noncomputable def midpointP029Radius2543 : ℝ := ((49928481130045985 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem midpointP029RoundCompute2543 :
    pairRound2542 (pairMul2542 midpointP029Factor2543 midpointP029Center2543) =
        midpointP029Rounded2543 := by
  cbv

theorem midpointP029RoundedError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP029Rounded2543‖ ≤ midpointP029Radius2543 := by
  have hr := embedPair_round_error2542 (pairMul2542 midpointP029Factor2543 midpointP029Center2543)
  rw [midpointP029RoundCompute2543, embedPair_mul2542] at hr
  have h := (midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP029Factor2543 * embedPair2542 midpointP029Center2543)
    (embedPair2542 midpointP029Rounded2543)).trans (add_le_add midpointP029DerivativeError2543 hr)
  apply h.trans
  norm_num [pairMagnitude2542, midpointP029Factor2543, midpointP029Error2543, rounding2542,
      midpointP029Radius2543]

theorem midpointP029DerivativeNorm2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩ midpointPosition2543‖ ≤ 1 := by
  have h := midpoint_triangle2543
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩ midpointPosition2543)
    (embedPair2542 midpointP029Rounded2543) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add midpointP029RoundedError2543 (embedPair_magnitude2542
      midpointP029Rounded2543))
  apply h'.trans
  norm_num [midpointP029Radius2543, pairMagnitude2542, midpointP029Rounded2543]

noncomputable def signedMidpointValue2543 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 midpointP000Rounded2543
  | 1 => embedPair2542 midpointP001Rounded2543
  | 2 => embedPair2542 midpointP002Rounded2543
  | 3 => embedPair2542 midpointP003Rounded2543
  | 4 => embedPair2542 midpointP004Rounded2543
  | 5 => embedPair2542 midpointP005Rounded2543
  | 6 => embedPair2542 midpointP006Rounded2543
  | 7 => embedPair2542 midpointP007Rounded2543
  | 8 => embedPair2542 midpointP008Rounded2543
  | 9 => embedPair2542 midpointP009Rounded2543
  | 10 => embedPair2542 midpointP010Rounded2543
  | 11 => embedPair2542 midpointP011Rounded2543
  | 12 => embedPair2542 midpointP012Rounded2543
  | 13 => embedPair2542 midpointP013Rounded2543
  | 14 => embedPair2542 midpointP014Rounded2543
  | 15 => embedPair2542 midpointP015Rounded2543
  | 16 => embedPair2542 midpointP016Rounded2543
  | 17 => embedPair2542 midpointP017Rounded2543
  | 18 => embedPair2542 midpointP018Rounded2543
  | 19 => embedPair2542 midpointP019Rounded2543
  | 20 => embedPair2542 midpointP020Rounded2543
  | 21 => embedPair2542 midpointP021Rounded2543
  | 22 => embedPair2542 midpointP022Rounded2543
  | 23 => embedPair2542 midpointP023Rounded2543
  | 24 => embedPair2542 midpointP024Rounded2543
  | 25 => embedPair2542 midpointP025Rounded2543
  | 26 => embedPair2542 midpointP026Rounded2543
  | 27 => embedPair2542 midpointP027Rounded2543
  | 28 => embedPair2542 midpointP028Rounded2543
  | 29 => embedPair2542 midpointP029Rounded2543
  | _ => 0

noncomputable def signedMidpointError2543 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => midpointP000Radius2543
  | 1 => midpointP001Radius2543
  | 2 => midpointP002Radius2543
  | 3 => midpointP003Radius2543
  | 4 => midpointP004Radius2543
  | 5 => midpointP005Radius2543
  | 6 => midpointP006Radius2543
  | 7 => midpointP007Radius2543
  | 8 => midpointP008Radius2543
  | 9 => midpointP009Radius2543
  | 10 => midpointP010Radius2543
  | 11 => midpointP011Radius2543
  | 12 => midpointP012Radius2543
  | 13 => midpointP013Radius2543
  | 14 => midpointP014Radius2543
  | 15 => midpointP015Radius2543
  | 16 => midpointP016Radius2543
  | 17 => midpointP017Radius2543
  | 18 => midpointP018Radius2543
  | 19 => midpointP019Radius2543
  | 20 => midpointP020Radius2543
  | 21 => midpointP021Radius2543
  | 22 => midpointP022Radius2543
  | 23 => midpointP023Radius2543
  | 24 => midpointP024Radius2543
  | 25 => midpointP025Radius2543
  | 26 => midpointP026Radius2543
  | 27 => midpointP027Radius2543
  | 28 => midpointP028Radius2543
  | 29 => midpointP029Radius2543
  | _ => 0

theorem signedMidpointExpError2543 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i midpointPosition2543 -
        signedMidpointValue2543 i‖ ≤ signedMidpointError2543 i := by
  fin_cases i
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP000RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP001RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP002RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP003RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP004RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP005RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP006RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP007RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP008RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP009RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP010RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP011RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP012RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP013RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP014RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP015RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP016RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP017RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP018RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP019RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP020RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP021RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP022RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP023RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP024RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP025RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP026RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP027RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP028RoundedError2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP029RoundedError2543

theorem signedMidpointUnitNorm2543 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i midpointPosition2543‖ ≤ 1 := by
  fin_cases i
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP000DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP001DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP002DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP003DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP004DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP005DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP006DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP007DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP008DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP009DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP010DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP011DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP012DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP013DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP014DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP015DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP016DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP017DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP018DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP019DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP020DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP021DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP022DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP023DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP024DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP025DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP026DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP027DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP028DerivativeNorm2543
  · simpa only [signedMidpointValue2543, signedMidpointError2543] using
      midpointP029DerivativeNorm2543

noncomputable def signedMidpointSum2543 : ℂ := ⟨(((-(((1044502350 * 10^40
        + 9410196738557565967665577165729331996395) * 10^40
        + 6245268370703810605396344852665217824306) * 10^40
        + 9860776679759846370790817150268923431453)) : ℝ) /
        (((5415370 * 10^40
        + 4963297165226140902034044603582742911628) * 10^40
        + 4339174837984293088793224180786254499995) * 10^40
        + 11922147613471467208908991351228465152)),
    (((((13468753328 * 10^40
        + 5173759174071386774418991620152234604320) * 10^40
        + 5461231794473780057304149703379326063790) * 10^40
        + 4452860461322371328258858271729304265121) : ℝ) /
        (((5415370 * 10^40
        + 4963297165226140902034044603582742911628) * 10^40
        + 4339174837984293088793224180786254499995) * 10^40
        + 11922147613471467208908991351228465152))⟩

noncomputable def signedMidpointUpper2543 : ℝ := ((997840737 : ℝ) /
        400000)

theorem signedMidpointSum_eq2543 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * signedMidpointValue2543 i) =
      signedMidpointSum2543 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, signedMidpointValue2543,
      signedMidpointSum2543, embedPair2542, midpointP000Rounded2543,
      midpointP001Rounded2543,
      midpointP002Rounded2543,
      midpointP003Rounded2543,
      midpointP004Rounded2543,
      midpointP005Rounded2543,
      midpointP006Rounded2543,
      midpointP007Rounded2543,
      midpointP008Rounded2543,
      midpointP009Rounded2543,
      midpointP010Rounded2543,
      midpointP011Rounded2543,
      midpointP012Rounded2543,
      midpointP013Rounded2543,
      midpointP014Rounded2543,
      midpointP015Rounded2543,
      midpointP016Rounded2543,
      midpointP017Rounded2543,
      midpointP018Rounded2543,
      midpointP019Rounded2543,
      midpointP020Rounded2543,
      midpointP021Rounded2543,
      midpointP022Rounded2543,
      midpointP023Rounded2543,
      midpointP024Rounded2543,
      midpointP025Rounded2543,
      midpointP026Rounded2543,
      midpointP027Rounded2543,
      midpointP028Rounded2543,
      midpointP029Rounded2543, Complex.mul_re, Complex.mul_im]

theorem signedMidpointSum_norm2543 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * signedMidpointValue2543 i‖ ≤ ((3118252303 : ℝ) /
        1250000) := by
  rw [signedMidpointSum_eq2543]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [signedMidpointSum2543]

theorem signedMidpointCharge2543 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * signedMidpointError2543 i) ≤ (1 : ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, signedMidpointError2543,
      midpointP000Radius2543,
      midpointP001Radius2543,
      midpointP002Radius2543,
      midpointP003Radius2543,
      midpointP004Radius2543,
      midpointP005Radius2543,
      midpointP006Radius2543,
      midpointP007Radius2543,
      midpointP008Radius2543,
      midpointP009Radius2543,
      midpointP010Radius2543,
      midpointP011Radius2543,
      midpointP012Radius2543,
      midpointP013Radius2543,
      midpointP014Radius2543,
      midpointP015Radius2543,
      midpointP016Radius2543,
      midpointP017Radius2543,
      midpointP018Radius2543,
      midpointP019Radius2543,
      midpointP020Radius2543,
      midpointP021Radius2543,
      midpointP022Radius2543,
      midpointP023Radius2543,
      midpointP024Radius2543,
      midpointP025Radius2543,
      midpointP026Radius2543,
      midpointP027Radius2543,
      midpointP028Radius2543,
      midpointP029Radius2543]

theorem signedMidpointUpper_le2543 :
    signedJetUpper2539 2 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 midpointPosition2543 ≤ signedMidpointUpper2543 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i midpointPosition2543‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * signedMidpointValue2543 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * signedMidpointError2543 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (signedMidpointExpError2543 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i midpointPosition2543‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (signedMidpointUnitNorm2543 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i midpointPosition2543‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 signedMidpointUpper2543
  linarith [signedMidpointSum_norm2543, signedMidpointCharge2543]

theorem weightedPhysical_second_midpoint_le2543 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        midpointPosition2543‖ ≤
      signedMidpointUpper2543 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i)) midpointPosition2543
  exact h.trans signedMidpointUpper_le2543

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.signedMidpointExpError2543
#print axioms ConnesWeilRH.Dev.signedMidpointSum_eq2543
#print axioms ConnesWeilRH.Dev.signedMidpointCharge2543
#print axioms ConnesWeilRH.Dev.signedMidpointUpper_le2543
#print axioms ConnesWeilRH.Dev.weightedPhysical_second_midpoint_le2543
