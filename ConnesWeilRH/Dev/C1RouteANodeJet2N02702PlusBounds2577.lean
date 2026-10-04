import ConnesWeilRH.Dev.C1RouteANodeJet2N02702Plus2577
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem nodeJet2N02702PlusPoint_triangle2577 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def nodeJet2N02702PlusPointP000Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP000Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02702PlusPointP000RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP000Factor2577
        nodeJet2N02702PlusPointP000Center2577) =
        nodeJet2N02702PlusPointP000Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP000RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP000Rounded2577‖ ≤
          nodeJet2N02702PlusPointP000Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP000Factor2577
      nodeJet2N02702PlusPointP000Center2577)
  rw [nodeJet2N02702PlusPointP000RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP000Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP000Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP000Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP000DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP000Factor2577,
      nodeJet2N02702PlusPointP000Error2577, rounding2542,
      nodeJet2N02702PlusPointP000Radius2577]

theorem nodeJet2N02702PlusPointP000DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP000Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP000RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP000Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP000Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP000Rounded2577]

def nodeJet2N02702PlusPointP001Rounded2577 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP001Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702PlusPointP001RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP001Factor2577
        nodeJet2N02702PlusPointP001Center2577) =
        nodeJet2N02702PlusPointP001Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP001RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP001Rounded2577‖ ≤
          nodeJet2N02702PlusPointP001Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP001Factor2577
      nodeJet2N02702PlusPointP001Center2577)
  rw [nodeJet2N02702PlusPointP001RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP001Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP001Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP001Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP001DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP001Factor2577,
      nodeJet2N02702PlusPointP001Error2577, rounding2542,
      nodeJet2N02702PlusPointP001Radius2577]

theorem nodeJet2N02702PlusPointP001DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP001Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP001RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP001Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP001Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP001Rounded2577]

def nodeJet2N02702PlusPointP002Rounded2577 : RatPair2542 :=
  (((766317 : ℚ) /
        633825300114114700748351602688),
    (((-1017423) : ℚ) /
        1267650600228229401496703205376))

noncomputable def nodeJet2N02702PlusPointP002Radius2577 : ℝ := ((2199023262781 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702PlusPointP002RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP002Factor2577
        nodeJet2N02702PlusPointP002Center2577) =
        nodeJet2N02702PlusPointP002Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP002RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP002Rounded2577‖ ≤
          nodeJet2N02702PlusPointP002Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP002Factor2577
      nodeJet2N02702PlusPointP002Center2577)
  rw [nodeJet2N02702PlusPointP002RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP002Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP002Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP002Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP002DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP002Factor2577,
      nodeJet2N02702PlusPointP002Error2577, rounding2542,
      nodeJet2N02702PlusPointP002Radius2577]

theorem nodeJet2N02702PlusPointP002DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP002Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP002RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP002Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP002Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP002Rounded2577]

def nodeJet2N02702PlusPointP003Rounded2577 : RatPair2542 :=
  (((15541463381173 : ℚ) /
        1267650600228229401496703205376),
    ((5113620283377 : ℚ) /
        1267650600228229401496703205376))

noncomputable def nodeJet2N02702PlusPointP003Radius2577 : ℝ := ((1140058075341 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02702PlusPointP003RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP003Factor2577
        nodeJet2N02702PlusPointP003Center2577) =
        nodeJet2N02702PlusPointP003Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP003RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP003Rounded2577‖ ≤
          nodeJet2N02702PlusPointP003Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP003Factor2577
      nodeJet2N02702PlusPointP003Center2577)
  rw [nodeJet2N02702PlusPointP003RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP003Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP003Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP003Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP003DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP003Factor2577,
      nodeJet2N02702PlusPointP003Error2577, rounding2542,
      nodeJet2N02702PlusPointP003Radius2577]

theorem nodeJet2N02702PlusPointP003DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP003Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP003RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP003Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP003Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP003Rounded2577]

def nodeJet2N02702PlusPointP004Rounded2577 : RatPair2542 :=
  (((5865245260357395 : ℚ) /
        1267650600228229401496703205376),
    (((-2228533276398335) : ℚ) /
        633825300114114700748351602688))

noncomputable def nodeJet2N02702PlusPointP004Radius2577 : ℝ := ((17543780436683 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02702PlusPointP004RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP004Factor2577
        nodeJet2N02702PlusPointP004Center2577) =
        nodeJet2N02702PlusPointP004Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP004RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP004Rounded2577‖ ≤
          nodeJet2N02702PlusPointP004Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP004Factor2577
      nodeJet2N02702PlusPointP004Center2577)
  rw [nodeJet2N02702PlusPointP004RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP004Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP004Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP004Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP004DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP004Factor2577,
      nodeJet2N02702PlusPointP004Error2577, rounding2542,
      nodeJet2N02702PlusPointP004Radius2577]

theorem nodeJet2N02702PlusPointP004DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP004Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP004RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP004Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP004Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP004Rounded2577]

def nodeJet2N02702PlusPointP005Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP005Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02702PlusPointP005RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP005Factor2577
        nodeJet2N02702PlusPointP005Center2577) =
        nodeJet2N02702PlusPointP005Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP005RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP005Rounded2577‖ ≤
          nodeJet2N02702PlusPointP005Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP005Factor2577
      nodeJet2N02702PlusPointP005Center2577)
  rw [nodeJet2N02702PlusPointP005RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP005Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP005Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP005Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP005DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP005Factor2577,
      nodeJet2N02702PlusPointP005Error2577, rounding2542,
      nodeJet2N02702PlusPointP005Radius2577]

theorem nodeJet2N02702PlusPointP005DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP005Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP005RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP005Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP005Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP005Rounded2577]

def nodeJet2N02702PlusPointP006Rounded2577 : RatPair2542 :=
  (((1 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP006Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702PlusPointP006RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP006Factor2577
        nodeJet2N02702PlusPointP006Center2577) =
        nodeJet2N02702PlusPointP006Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP006RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP006Rounded2577‖ ≤
          nodeJet2N02702PlusPointP006Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP006Factor2577
      nodeJet2N02702PlusPointP006Center2577)
  rw [nodeJet2N02702PlusPointP006RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP006Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP006Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP006Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP006DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP006Factor2577,
      nodeJet2N02702PlusPointP006Error2577, rounding2542,
      nodeJet2N02702PlusPointP006Radius2577]

theorem nodeJet2N02702PlusPointP006DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP006Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP006RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP006Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP006Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP006Rounded2577]

def nodeJet2N02702PlusPointP007Rounded2577 : RatPair2542 :=
  (((1899255878273 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP007Radius2577 : ℝ := ((549824766045 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02702PlusPointP007RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP007Factor2577
        nodeJet2N02702PlusPointP007Center2577) =
        nodeJet2N02702PlusPointP007Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP007RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP007Rounded2577‖ ≤
          nodeJet2N02702PlusPointP007Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP007Factor2577
      nodeJet2N02702PlusPointP007Center2577)
  rw [nodeJet2N02702PlusPointP007RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP007Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP007Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP007Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP007DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP007Factor2577,
      nodeJet2N02702PlusPointP007Error2577, rounding2542,
      nodeJet2N02702PlusPointP007Radius2577]

theorem nodeJet2N02702PlusPointP007DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP007Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP007RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP007Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP007Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP007Rounded2577]

def nodeJet2N02702PlusPointP008Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP008Radius2577 : ℝ := ((2199119126991 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702PlusPointP008RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP008Factor2577
        nodeJet2N02702PlusPointP008Center2577) =
        nodeJet2N02702PlusPointP008Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP008RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP008Rounded2577‖ ≤
          nodeJet2N02702PlusPointP008Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP008Factor2577
      nodeJet2N02702PlusPointP008Center2577)
  rw [nodeJet2N02702PlusPointP008RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP008Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP008Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP008Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP008DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP008Factor2577,
      nodeJet2N02702PlusPointP008Error2577, rounding2542,
      nodeJet2N02702PlusPointP008Radius2577]

theorem nodeJet2N02702PlusPointP008DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP008Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP008RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP008Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP008Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP008Rounded2577]

def nodeJet2N02702PlusPointP009Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP009Radius2577 : ℝ := ((2199119127177 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702PlusPointP009RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP009Factor2577
        nodeJet2N02702PlusPointP009Center2577) =
        nodeJet2N02702PlusPointP009Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP009RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP009Rounded2577‖ ≤
          nodeJet2N02702PlusPointP009Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP009Factor2577
      nodeJet2N02702PlusPointP009Center2577)
  rw [nodeJet2N02702PlusPointP009RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP009Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP009Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP009Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP009DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP009Factor2577,
      nodeJet2N02702PlusPointP009Error2577, rounding2542,
      nodeJet2N02702PlusPointP009Radius2577]

theorem nodeJet2N02702PlusPointP009DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP009Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP009RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP009Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP009Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP009Rounded2577]

def nodeJet2N02702PlusPointP010Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP010Radius2577 : ℝ := ((2199119127285 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702PlusPointP010RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP010Factor2577
        nodeJet2N02702PlusPointP010Center2577) =
        nodeJet2N02702PlusPointP010Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP010RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP010Rounded2577‖ ≤
          nodeJet2N02702PlusPointP010Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP010Factor2577
      nodeJet2N02702PlusPointP010Center2577)
  rw [nodeJet2N02702PlusPointP010RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP010Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP010Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP010Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP010DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP010Factor2577,
      nodeJet2N02702PlusPointP010Error2577, rounding2542,
      nodeJet2N02702PlusPointP010Radius2577]

theorem nodeJet2N02702PlusPointP010DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP010Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP010RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP010Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP010Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP010Rounded2577]

def nodeJet2N02702PlusPointP011Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP011Radius2577 : ℝ := ((2199119127357 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702PlusPointP011RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP011Factor2577
        nodeJet2N02702PlusPointP011Center2577) =
        nodeJet2N02702PlusPointP011Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP011RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP011Rounded2577‖ ≤
          nodeJet2N02702PlusPointP011Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP011Factor2577
      nodeJet2N02702PlusPointP011Center2577)
  rw [nodeJet2N02702PlusPointP011RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP011Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP011Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP011Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP011DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP011Factor2577,
      nodeJet2N02702PlusPointP011Error2577, rounding2542,
      nodeJet2N02702PlusPointP011Radius2577]

theorem nodeJet2N02702PlusPointP011DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP011Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP011RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP011Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP011Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP011Rounded2577]

def nodeJet2N02702PlusPointP012Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP012Radius2577 : ℝ := ((274889890929 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem nodeJet2N02702PlusPointP012RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP012Factor2577
        nodeJet2N02702PlusPointP012Center2577) =
        nodeJet2N02702PlusPointP012Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP012RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP012Rounded2577‖ ≤
          nodeJet2N02702PlusPointP012Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP012Factor2577
      nodeJet2N02702PlusPointP012Center2577)
  rw [nodeJet2N02702PlusPointP012RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP012Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP012Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP012Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP012DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP012Factor2577,
      nodeJet2N02702PlusPointP012Error2577, rounding2542,
      nodeJet2N02702PlusPointP012Radius2577]

theorem nodeJet2N02702PlusPointP012DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP012Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP012RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP012Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP012Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP012Rounded2577]

def nodeJet2N02702PlusPointP013Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP013Radius2577 : ℝ := ((549779781875 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02702PlusPointP013RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP013Factor2577
        nodeJet2N02702PlusPointP013Center2577) =
        nodeJet2N02702PlusPointP013Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP013RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP013Rounded2577‖ ≤
          nodeJet2N02702PlusPointP013Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP013Factor2577
      nodeJet2N02702PlusPointP013Center2577)
  rw [nodeJet2N02702PlusPointP013RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP013Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP013Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP013Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP013DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP013Factor2577,
      nodeJet2N02702PlusPointP013Error2577, rounding2542,
      nodeJet2N02702PlusPointP013Radius2577]

theorem nodeJet2N02702PlusPointP013DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP013Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP013RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP013Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP013Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP013Rounded2577]

def nodeJet2N02702PlusPointP014Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP014Radius2577 : ℝ := ((2199119127625 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702PlusPointP014RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP014Factor2577
        nodeJet2N02702PlusPointP014Center2577) =
        nodeJet2N02702PlusPointP014Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP014RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP014Rounded2577‖ ≤
          nodeJet2N02702PlusPointP014Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP014Factor2577
      nodeJet2N02702PlusPointP014Center2577)
  rw [nodeJet2N02702PlusPointP014RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP014Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP014Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP014Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP014DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP014Factor2577,
      nodeJet2N02702PlusPointP014Error2577, rounding2542,
      nodeJet2N02702PlusPointP014Radius2577]

theorem nodeJet2N02702PlusPointP014DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP014Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP014RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP014Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP014Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP014Rounded2577]

def nodeJet2N02702PlusPointP015Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP015Radius2577 : ℝ := ((549779781929 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02702PlusPointP015RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP015Factor2577
        nodeJet2N02702PlusPointP015Center2577) =
        nodeJet2N02702PlusPointP015Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP015RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP015Rounded2577‖ ≤
          nodeJet2N02702PlusPointP015Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP015Factor2577
      nodeJet2N02702PlusPointP015Center2577)
  rw [nodeJet2N02702PlusPointP015RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP015Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP015Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP015Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP015DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP015Factor2577,
      nodeJet2N02702PlusPointP015Error2577, rounding2542,
      nodeJet2N02702PlusPointP015Radius2577]

theorem nodeJet2N02702PlusPointP015DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP015Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP015RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP015Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP015Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP015Rounded2577]

def nodeJet2N02702PlusPointP016Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP016Radius2577 : ℝ := ((2199119127781 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702PlusPointP016RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP016Factor2577
        nodeJet2N02702PlusPointP016Center2577) =
        nodeJet2N02702PlusPointP016Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP016RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP016Rounded2577‖ ≤
          nodeJet2N02702PlusPointP016Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP016Factor2577
      nodeJet2N02702PlusPointP016Center2577)
  rw [nodeJet2N02702PlusPointP016RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP016Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP016Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP016Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP016DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP016Factor2577,
      nodeJet2N02702PlusPointP016Error2577, rounding2542,
      nodeJet2N02702PlusPointP016Radius2577]

theorem nodeJet2N02702PlusPointP016DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP016Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP016RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP016Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP016Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP016Rounded2577]

def nodeJet2N02702PlusPointP017Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP017Radius2577 : ℝ := ((2199119127907 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702PlusPointP017RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP017Factor2577
        nodeJet2N02702PlusPointP017Center2577) =
        nodeJet2N02702PlusPointP017Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP017RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP017Rounded2577‖ ≤
          nodeJet2N02702PlusPointP017Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP017Factor2577
      nodeJet2N02702PlusPointP017Center2577)
  rw [nodeJet2N02702PlusPointP017RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP017Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP017Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP017Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP017DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP017Factor2577,
      nodeJet2N02702PlusPointP017Error2577, rounding2542,
      nodeJet2N02702PlusPointP017Radius2577]

theorem nodeJet2N02702PlusPointP017DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP017Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP017RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP017Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP017Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP017Rounded2577]

def nodeJet2N02702PlusPointP018Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP018Radius2577 : ℝ := ((2199119127955 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702PlusPointP018RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP018Factor2577
        nodeJet2N02702PlusPointP018Center2577) =
        nodeJet2N02702PlusPointP018Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP018RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP018Rounded2577‖ ≤
          nodeJet2N02702PlusPointP018Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP018Factor2577
      nodeJet2N02702PlusPointP018Center2577)
  rw [nodeJet2N02702PlusPointP018RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP018Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP018Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP018Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP018DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP018Factor2577,
      nodeJet2N02702PlusPointP018Error2577, rounding2542,
      nodeJet2N02702PlusPointP018Radius2577]

theorem nodeJet2N02702PlusPointP018DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP018Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP018RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP018Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP018Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP018Rounded2577]

def nodeJet2N02702PlusPointP019Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP019Radius2577 : ℝ := ((1099559564021 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02702PlusPointP019RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP019Factor2577
        nodeJet2N02702PlusPointP019Center2577) =
        nodeJet2N02702PlusPointP019Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP019RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP019Rounded2577‖ ≤
          nodeJet2N02702PlusPointP019Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP019Factor2577
      nodeJet2N02702PlusPointP019Center2577)
  rw [nodeJet2N02702PlusPointP019RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP019Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP019Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP019Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP019DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP019Factor2577,
      nodeJet2N02702PlusPointP019Error2577, rounding2542,
      nodeJet2N02702PlusPointP019Radius2577]

theorem nodeJet2N02702PlusPointP019DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP019Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP019RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP019Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP019Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP019Rounded2577]

def nodeJet2N02702PlusPointP020Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP020Radius2577 : ℝ := ((274889891017 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem nodeJet2N02702PlusPointP020RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP020Factor2577
        nodeJet2N02702PlusPointP020Center2577) =
        nodeJet2N02702PlusPointP020Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP020RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP020Rounded2577‖ ≤
          nodeJet2N02702PlusPointP020Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP020Factor2577
      nodeJet2N02702PlusPointP020Center2577)
  rw [nodeJet2N02702PlusPointP020RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP020Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP020Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP020Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP020DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP020Factor2577,
      nodeJet2N02702PlusPointP020Error2577, rounding2542,
      nodeJet2N02702PlusPointP020Radius2577]

theorem nodeJet2N02702PlusPointP020DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP020Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP020RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP020Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP020Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP020Rounded2577]

def nodeJet2N02702PlusPointP021Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP021Radius2577 : ℝ := ((1099559564107 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02702PlusPointP021RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP021Factor2577
        nodeJet2N02702PlusPointP021Center2577) =
        nodeJet2N02702PlusPointP021Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP021RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP021Rounded2577‖ ≤
          nodeJet2N02702PlusPointP021Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP021Factor2577
      nodeJet2N02702PlusPointP021Center2577)
  rw [nodeJet2N02702PlusPointP021RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP021Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP021Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP021Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP021DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP021Factor2577,
      nodeJet2N02702PlusPointP021Error2577, rounding2542,
      nodeJet2N02702PlusPointP021Radius2577]

theorem nodeJet2N02702PlusPointP021DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP021Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP021RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP021Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP021Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP021Rounded2577]

def nodeJet2N02702PlusPointP022Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP022Radius2577 : ℝ := ((1099559564127 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02702PlusPointP022RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP022Factor2577
        nodeJet2N02702PlusPointP022Center2577) =
        nodeJet2N02702PlusPointP022Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP022RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP022Rounded2577‖ ≤
          nodeJet2N02702PlusPointP022Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP022Factor2577
      nodeJet2N02702PlusPointP022Center2577)
  rw [nodeJet2N02702PlusPointP022RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP022Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP022Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP022Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP022DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP022Factor2577,
      nodeJet2N02702PlusPointP022Error2577, rounding2542,
      nodeJet2N02702PlusPointP022Radius2577]

theorem nodeJet2N02702PlusPointP022DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP022Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP022RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP022Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP022Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP022Rounded2577]

def nodeJet2N02702PlusPointP023Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP023Radius2577 : ℝ := ((1099559564185 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02702PlusPointP023RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP023Factor2577
        nodeJet2N02702PlusPointP023Center2577) =
        nodeJet2N02702PlusPointP023Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP023RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP023Rounded2577‖ ≤
          nodeJet2N02702PlusPointP023Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP023Factor2577
      nodeJet2N02702PlusPointP023Center2577)
  rw [nodeJet2N02702PlusPointP023RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP023Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP023Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP023Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP023DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP023Factor2577,
      nodeJet2N02702PlusPointP023Error2577, rounding2542,
      nodeJet2N02702PlusPointP023Radius2577]

theorem nodeJet2N02702PlusPointP023DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP023Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP023RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP023Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP023Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP023Rounded2577]

def nodeJet2N02702PlusPointP024Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP024Radius2577 : ℝ := ((2199119128423 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702PlusPointP024RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP024Factor2577
        nodeJet2N02702PlusPointP024Center2577) =
        nodeJet2N02702PlusPointP024Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP024RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP024Rounded2577‖ ≤
          nodeJet2N02702PlusPointP024Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP024Factor2577
      nodeJet2N02702PlusPointP024Center2577)
  rw [nodeJet2N02702PlusPointP024RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP024Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP024Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP024Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP024DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP024Factor2577,
      nodeJet2N02702PlusPointP024Error2577, rounding2542,
      nodeJet2N02702PlusPointP024Radius2577]

theorem nodeJet2N02702PlusPointP024DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP024Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP024RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP024Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP024Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP024Rounded2577]

def nodeJet2N02702PlusPointP025Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP025Radius2577 : ℝ := ((1099559564245 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02702PlusPointP025RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP025Factor2577
        nodeJet2N02702PlusPointP025Center2577) =
        nodeJet2N02702PlusPointP025Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP025RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP025Rounded2577‖ ≤
          nodeJet2N02702PlusPointP025Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP025Factor2577
      nodeJet2N02702PlusPointP025Center2577)
  rw [nodeJet2N02702PlusPointP025RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP025Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP025Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP025Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP025DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP025Factor2577,
      nodeJet2N02702PlusPointP025Error2577, rounding2542,
      nodeJet2N02702PlusPointP025Radius2577]

theorem nodeJet2N02702PlusPointP025DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP025Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP025RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP025Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP025Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP025Rounded2577]

def nodeJet2N02702PlusPointP026Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP026Radius2577 : ℝ := ((1099559564279 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02702PlusPointP026RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP026Factor2577
        nodeJet2N02702PlusPointP026Center2577) =
        nodeJet2N02702PlusPointP026Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP026RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP026Rounded2577‖ ≤
          nodeJet2N02702PlusPointP026Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP026Factor2577
      nodeJet2N02702PlusPointP026Center2577)
  rw [nodeJet2N02702PlusPointP026RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP026Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP026Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP026Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP026DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP026Factor2577,
      nodeJet2N02702PlusPointP026Error2577, rounding2542,
      nodeJet2N02702PlusPointP026Radius2577]

theorem nodeJet2N02702PlusPointP026DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP026Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP026RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP026Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP026Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP026Rounded2577]

def nodeJet2N02702PlusPointP027Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP027Radius2577 : ℝ := ((137444945541 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem nodeJet2N02702PlusPointP027RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP027Factor2577
        nodeJet2N02702PlusPointP027Center2577) =
        nodeJet2N02702PlusPointP027Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP027RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP027Rounded2577‖ ≤
          nodeJet2N02702PlusPointP027Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP027Factor2577
      nodeJet2N02702PlusPointP027Center2577)
  rw [nodeJet2N02702PlusPointP027RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP027Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP027Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP027Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP027DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP027Factor2577,
      nodeJet2N02702PlusPointP027Error2577, rounding2542,
      nodeJet2N02702PlusPointP027Radius2577]

theorem nodeJet2N02702PlusPointP027DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP027Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP027RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP027Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP027Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP027Rounded2577]

def nodeJet2N02702PlusPointP028Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP028Radius2577 : ℝ := ((2199119128695 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702PlusPointP028RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP028Factor2577
        nodeJet2N02702PlusPointP028Center2577) =
        nodeJet2N02702PlusPointP028Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP028RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP028Rounded2577‖ ≤
          nodeJet2N02702PlusPointP028Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP028Factor2577
      nodeJet2N02702PlusPointP028Center2577)
  rw [nodeJet2N02702PlusPointP028RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP028Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP028Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP028Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP028DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP028Factor2577,
      nodeJet2N02702PlusPointP028Error2577, rounding2542,
      nodeJet2N02702PlusPointP028Radius2577]

theorem nodeJet2N02702PlusPointP028DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP028Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP028RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP028Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP028Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP028Rounded2577]

def nodeJet2N02702PlusPointP029Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702PlusPointP029Radius2577 : ℝ := ((2199119128755 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702PlusPointP029RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702PlusPointP029Factor2577
        nodeJet2N02702PlusPointP029Center2577) =
        nodeJet2N02702PlusPointP029Rounded2577 := by
  cbv

theorem nodeJet2N02702PlusPointP029RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02702PlusPointPosition2577 -
      embedPair2542 nodeJet2N02702PlusPointP029Rounded2577‖ ≤
          nodeJet2N02702PlusPointP029Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702PlusPointP029Factor2577
      nodeJet2N02702PlusPointP029Center2577)
  rw [nodeJet2N02702PlusPointP029RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP029Factor2577 * embedPair2542
        nodeJet2N02702PlusPointP029Center2577)
    (embedPair2542 nodeJet2N02702PlusPointP029Rounded2577)).trans (add_le_add
        nodeJet2N02702PlusPointP029DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702PlusPointP029Factor2577,
      nodeJet2N02702PlusPointP029Error2577, rounding2542,
      nodeJet2N02702PlusPointP029Radius2577]

theorem nodeJet2N02702PlusPointP029DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02702PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02702PlusPointPosition2577)
    (embedPair2542 nodeJet2N02702PlusPointP029Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702PlusPointP029RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702PlusPointP029Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702PlusPointP029Radius2577, pairMagnitude2542,
      nodeJet2N02702PlusPointP029Rounded2577]

noncomputable def nodeJet2N02702PlusSignedValue2577 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 nodeJet2N02702PlusPointP000Rounded2577
  | 1 => embedPair2542 nodeJet2N02702PlusPointP001Rounded2577
  | 2 => embedPair2542 nodeJet2N02702PlusPointP002Rounded2577
  | 3 => embedPair2542 nodeJet2N02702PlusPointP003Rounded2577
  | 4 => embedPair2542 nodeJet2N02702PlusPointP004Rounded2577
  | 5 => embedPair2542 nodeJet2N02702PlusPointP005Rounded2577
  | 6 => embedPair2542 nodeJet2N02702PlusPointP006Rounded2577
  | 7 => embedPair2542 nodeJet2N02702PlusPointP007Rounded2577
  | 8 => embedPair2542 nodeJet2N02702PlusPointP008Rounded2577
  | 9 => embedPair2542 nodeJet2N02702PlusPointP009Rounded2577
  | 10 => embedPair2542 nodeJet2N02702PlusPointP010Rounded2577
  | 11 => embedPair2542 nodeJet2N02702PlusPointP011Rounded2577
  | 12 => embedPair2542 nodeJet2N02702PlusPointP012Rounded2577
  | 13 => embedPair2542 nodeJet2N02702PlusPointP013Rounded2577
  | 14 => embedPair2542 nodeJet2N02702PlusPointP014Rounded2577
  | 15 => embedPair2542 nodeJet2N02702PlusPointP015Rounded2577
  | 16 => embedPair2542 nodeJet2N02702PlusPointP016Rounded2577
  | 17 => embedPair2542 nodeJet2N02702PlusPointP017Rounded2577
  | 18 => embedPair2542 nodeJet2N02702PlusPointP018Rounded2577
  | 19 => embedPair2542 nodeJet2N02702PlusPointP019Rounded2577
  | 20 => embedPair2542 nodeJet2N02702PlusPointP020Rounded2577
  | 21 => embedPair2542 nodeJet2N02702PlusPointP021Rounded2577
  | 22 => embedPair2542 nodeJet2N02702PlusPointP022Rounded2577
  | 23 => embedPair2542 nodeJet2N02702PlusPointP023Rounded2577
  | 24 => embedPair2542 nodeJet2N02702PlusPointP024Rounded2577
  | 25 => embedPair2542 nodeJet2N02702PlusPointP025Rounded2577
  | 26 => embedPair2542 nodeJet2N02702PlusPointP026Rounded2577
  | 27 => embedPair2542 nodeJet2N02702PlusPointP027Rounded2577
  | 28 => embedPair2542 nodeJet2N02702PlusPointP028Rounded2577
  | 29 => embedPair2542 nodeJet2N02702PlusPointP029Rounded2577
  | _ => 0

noncomputable def nodeJet2N02702PlusSignedError2577 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => nodeJet2N02702PlusPointP000Radius2577
  | 1 => nodeJet2N02702PlusPointP001Radius2577
  | 2 => nodeJet2N02702PlusPointP002Radius2577
  | 3 => nodeJet2N02702PlusPointP003Radius2577
  | 4 => nodeJet2N02702PlusPointP004Radius2577
  | 5 => nodeJet2N02702PlusPointP005Radius2577
  | 6 => nodeJet2N02702PlusPointP006Radius2577
  | 7 => nodeJet2N02702PlusPointP007Radius2577
  | 8 => nodeJet2N02702PlusPointP008Radius2577
  | 9 => nodeJet2N02702PlusPointP009Radius2577
  | 10 => nodeJet2N02702PlusPointP010Radius2577
  | 11 => nodeJet2N02702PlusPointP011Radius2577
  | 12 => nodeJet2N02702PlusPointP012Radius2577
  | 13 => nodeJet2N02702PlusPointP013Radius2577
  | 14 => nodeJet2N02702PlusPointP014Radius2577
  | 15 => nodeJet2N02702PlusPointP015Radius2577
  | 16 => nodeJet2N02702PlusPointP016Radius2577
  | 17 => nodeJet2N02702PlusPointP017Radius2577
  | 18 => nodeJet2N02702PlusPointP018Radius2577
  | 19 => nodeJet2N02702PlusPointP019Radius2577
  | 20 => nodeJet2N02702PlusPointP020Radius2577
  | 21 => nodeJet2N02702PlusPointP021Radius2577
  | 22 => nodeJet2N02702PlusPointP022Radius2577
  | 23 => nodeJet2N02702PlusPointP023Radius2577
  | 24 => nodeJet2N02702PlusPointP024Radius2577
  | 25 => nodeJet2N02702PlusPointP025Radius2577
  | 26 => nodeJet2N02702PlusPointP026Radius2577
  | 27 => nodeJet2N02702PlusPointP027Radius2577
  | 28 => nodeJet2N02702PlusPointP028Radius2577
  | 29 => nodeJet2N02702PlusPointP029Radius2577
  | _ => 0

theorem nodeJet2N02702PlusSignedExpError2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02702PlusPointPosition2577 -
        nodeJet2N02702PlusSignedValue2577 i‖ ≤ nodeJet2N02702PlusSignedError2577 i := by
  fin_cases i
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP000RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP001RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP002RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP003RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP004RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP005RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP006RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP007RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP008RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP009RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP010RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP011RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP012RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP013RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP014RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP015RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP016RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP017RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP018RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP019RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP020RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP021RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP022RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP023RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP024RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP025RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP026RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP027RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP028RoundedError2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP029RoundedError2577

theorem nodeJet2N02702PlusSignedUnitNorm2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02702PlusPointPosition2577‖ ≤ 1 :=
        by
  fin_cases i
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP000DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP001DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP002DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP003DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP004DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP005DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP006DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP007DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP008DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP009DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP010DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP011DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP012DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP013DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP014DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP015DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP016DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP017DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP018DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP019DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP020DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP021DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP022DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP023DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP024DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP025DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP026DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP027DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP028DerivativeNorm2577
  · simpa only [nodeJet2N02702PlusSignedValue2577, nodeJet2N02702PlusSignedError2577] using
      nodeJet2N02702PlusPointP029DerivativeNorm2577

noncomputable def nodeJet2N02702PlusSignedSum2577 : ℂ := ⟨(((-(((186840735616 * 10^40
        + 2478453736074937682452055049993468960993) * 10^40
        + 2617739282480575022361294655827975617631) * 10^40
        + 8664806885330955869589676860917109525343)) : ℝ) /
        (((177450860423 * 10^40
        + 7321510130185077851573570199319728240522) * 10^40
        + 6081091069315933576369956003987455836199) * 10^40
        + 664932998233037501529828597054346100736)),
    (((((590305578065 * 10^40
        + 8182298969429603610508401977795069231144) * 10^40
        + 2248941657851198489996301960692249686206) * 10^40
        + 8365705287380627667118467002497988756085) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888))⟩

noncomputable def nodeJet2N02702PlusSignedUpper2577 : ℝ := ((56602561 : ℝ) /
        50000000)

theorem nodeJet2N02702PlusSignedSum_eq2577 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02702PlusSignedValue2577 i) =
      nodeJet2N02702PlusSignedSum2577 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        nodeJet2N02702PlusSignedValue2577,
      nodeJet2N02702PlusSignedSum2577, embedPair2542, nodeJet2N02702PlusPointP000Rounded2577,
      nodeJet2N02702PlusPointP001Rounded2577,
      nodeJet2N02702PlusPointP002Rounded2577,
      nodeJet2N02702PlusPointP003Rounded2577,
      nodeJet2N02702PlusPointP004Rounded2577,
      nodeJet2N02702PlusPointP005Rounded2577,
      nodeJet2N02702PlusPointP006Rounded2577,
      nodeJet2N02702PlusPointP007Rounded2577,
      nodeJet2N02702PlusPointP008Rounded2577,
      nodeJet2N02702PlusPointP009Rounded2577,
      nodeJet2N02702PlusPointP010Rounded2577,
      nodeJet2N02702PlusPointP011Rounded2577,
      nodeJet2N02702PlusPointP012Rounded2577,
      nodeJet2N02702PlusPointP013Rounded2577,
      nodeJet2N02702PlusPointP014Rounded2577,
      nodeJet2N02702PlusPointP015Rounded2577,
      nodeJet2N02702PlusPointP016Rounded2577,
      nodeJet2N02702PlusPointP017Rounded2577,
      nodeJet2N02702PlusPointP018Rounded2577,
      nodeJet2N02702PlusPointP019Rounded2577,
      nodeJet2N02702PlusPointP020Rounded2577,
      nodeJet2N02702PlusPointP021Rounded2577,
      nodeJet2N02702PlusPointP022Rounded2577,
      nodeJet2N02702PlusPointP023Rounded2577,
      nodeJet2N02702PlusPointP024Rounded2577,
      nodeJet2N02702PlusPointP025Rounded2577,
      nodeJet2N02702PlusPointP026Rounded2577,
      nodeJet2N02702PlusPointP027Rounded2577,
      nodeJet2N02702PlusPointP028Rounded2577,
      nodeJet2N02702PlusPointP029Rounded2577, Complex.mul_re, Complex.mul_im]

theorem nodeJet2N02702PlusSignedSum_norm2577 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02702PlusSignedValue2577 i‖ ≤
        ((14150639 :
        ℝ) /
        12500000) := by
  rw [nodeJet2N02702PlusSignedSum_eq2577]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [nodeJet2N02702PlusSignedSum2577]

theorem nodeJet2N02702PlusSignedCharge2577 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02702PlusSignedError2577 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      nodeJet2N02702PlusSignedError2577, nodeJet2N02702PlusPointP000Radius2577,
      nodeJet2N02702PlusPointP001Radius2577,
      nodeJet2N02702PlusPointP002Radius2577,
      nodeJet2N02702PlusPointP003Radius2577,
      nodeJet2N02702PlusPointP004Radius2577,
      nodeJet2N02702PlusPointP005Radius2577,
      nodeJet2N02702PlusPointP006Radius2577,
      nodeJet2N02702PlusPointP007Radius2577,
      nodeJet2N02702PlusPointP008Radius2577,
      nodeJet2N02702PlusPointP009Radius2577,
      nodeJet2N02702PlusPointP010Radius2577,
      nodeJet2N02702PlusPointP011Radius2577,
      nodeJet2N02702PlusPointP012Radius2577,
      nodeJet2N02702PlusPointP013Radius2577,
      nodeJet2N02702PlusPointP014Radius2577,
      nodeJet2N02702PlusPointP015Radius2577,
      nodeJet2N02702PlusPointP016Radius2577,
      nodeJet2N02702PlusPointP017Radius2577,
      nodeJet2N02702PlusPointP018Radius2577,
      nodeJet2N02702PlusPointP019Radius2577,
      nodeJet2N02702PlusPointP020Radius2577,
      nodeJet2N02702PlusPointP021Radius2577,
      nodeJet2N02702PlusPointP022Radius2577,
      nodeJet2N02702PlusPointP023Radius2577,
      nodeJet2N02702PlusPointP024Radius2577,
      nodeJet2N02702PlusPointP025Radius2577,
      nodeJet2N02702PlusPointP026Radius2577,
      nodeJet2N02702PlusPointP027Radius2577,
      nodeJet2N02702PlusPointP028Radius2577,
      nodeJet2N02702PlusPointP029Radius2577]

theorem nodeJet2N02702PlusSignedUpper_le2577 :
    signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 nodeJet2N02702PlusPointPosition2577 ≤ nodeJet2N02702PlusSignedUpper2577
          := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02702PlusPointPosition2577‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02702PlusSignedValue2577 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02702PlusSignedError2577 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (nodeJet2N02702PlusSignedExpError2577
        i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02702PlusPointPosition2577‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (nodeJet2N02702PlusSignedUnitNorm2577 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02702PlusPointPosition2577‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 nodeJet2N02702PlusSignedUpper2577
  linarith [nodeJet2N02702PlusSignedSum_norm2577, nodeJet2N02702PlusSignedCharge2577]

theorem nodeJet2N02702PlusPhysical2577 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        nodeJet2N02702PlusPointPosition2577‖ ≤
      nodeJet2N02702PlusSignedUpper2577 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        nodeJet2N02702PlusPointPosition2577
  exact h.trans nodeJet2N02702PlusSignedUpper_le2577

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.nodeJet2N02702PlusSignedExpError2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02702PlusSignedSum_eq2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02702PlusSignedCharge2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02702PlusSignedUpper_le2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02702PlusPhysical2577
