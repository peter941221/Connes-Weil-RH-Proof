import ConnesWeilRH.Dev.C1RouteANodeJet2N02704Minus2577
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem nodeJet2N02704MinusPoint_triangle2577 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def nodeJet2N02704MinusPointP000Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP000Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02704MinusPointP000RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP000Factor2577
        nodeJet2N02704MinusPointP000Center2577) =
        nodeJet2N02704MinusPointP000Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP000RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP000Rounded2577‖ ≤
          nodeJet2N02704MinusPointP000Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP000Factor2577
      nodeJet2N02704MinusPointP000Center2577)
  rw [nodeJet2N02704MinusPointP000RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP000Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP000Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP000Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP000DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP000Factor2577,
      nodeJet2N02704MinusPointP000Error2577, rounding2542,
      nodeJet2N02704MinusPointP000Radius2577]

theorem nodeJet2N02704MinusPointP000DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP000Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP000RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP000Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP000Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP000Rounded2577]

def nodeJet2N02704MinusPointP001Rounded2577 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP001Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP001RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP001Factor2577
        nodeJet2N02704MinusPointP001Center2577) =
        nodeJet2N02704MinusPointP001Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP001RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP001Rounded2577‖ ≤
          nodeJet2N02704MinusPointP001Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP001Factor2577
      nodeJet2N02704MinusPointP001Center2577)
  rw [nodeJet2N02704MinusPointP001RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP001Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP001Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP001Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP001DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP001Factor2577,
      nodeJet2N02704MinusPointP001Error2577, rounding2542,
      nodeJet2N02704MinusPointP001Radius2577]

theorem nodeJet2N02704MinusPointP001DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP001Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP001RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP001Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP001Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP001Rounded2577]

def nodeJet2N02704MinusPointP002Rounded2577 : RatPair2542 :=
  (((19667589 : ℚ) /
        633825300114114700748351602688),
    (((-19327351) : ℚ) /
        1267650600228229401496703205376))

noncomputable def nodeJet2N02704MinusPointP002Radius2577 : ℝ := ((2199023422987 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP002RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP002Factor2577
        nodeJet2N02704MinusPointP002Center2577) =
        nodeJet2N02704MinusPointP002Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP002RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP002Rounded2577‖ ≤
          nodeJet2N02704MinusPointP002Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP002Factor2577
      nodeJet2N02704MinusPointP002Center2577)
  rw [nodeJet2N02704MinusPointP002RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP002Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP002Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP002Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP002DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP002Factor2577,
      nodeJet2N02704MinusPointP002Error2577, rounding2542,
      nodeJet2N02704MinusPointP002Radius2577]

theorem nodeJet2N02704MinusPointP002DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP002Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP002RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP002Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP002Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP002Rounded2577]

def nodeJet2N02704MinusPointP003Rounded2577 : RatPair2542 :=
  (((329147362685813 : ℚ) /
        1267650600228229401496703205376),
    ((10313388535581 : ℚ) /
        79228162514264337593543950336))

noncomputable def nodeJet2N02704MinusPointP003Radius2577 : ℝ := ((4014290814563 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP003RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP003Factor2577
        nodeJet2N02704MinusPointP003Center2577) =
        nodeJet2N02704MinusPointP003Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP003RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP003Rounded2577‖ ≤
          nodeJet2N02704MinusPointP003Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP003Factor2577
      nodeJet2N02704MinusPointP003Center2577)
  rw [nodeJet2N02704MinusPointP003RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP003Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP003Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP003Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP003DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP003Factor2577,
      nodeJet2N02704MinusPointP003Error2577, rounding2542,
      nodeJet2N02704MinusPointP003Radius2577]

theorem nodeJet2N02704MinusPointP003DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP003Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP003RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP003Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP003Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP003Rounded2577]

def nodeJet2N02704MinusPointP004Rounded2577 : RatPair2542 :=
  (((57131960139463293 : ℚ) /
        633825300114114700748351602688),
    (((-58837125104395075) : ℚ) /
        633825300114114700748351602688))

noncomputable def nodeJet2N02704MinusPointP004Radius2577 : ℝ := ((717443802047309 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP004RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP004Factor2577
        nodeJet2N02704MinusPointP004Center2577) =
        nodeJet2N02704MinusPointP004Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP004RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP004Rounded2577‖ ≤
          nodeJet2N02704MinusPointP004Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP004Factor2577
      nodeJet2N02704MinusPointP004Center2577)
  rw [nodeJet2N02704MinusPointP004RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP004Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP004Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP004Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP004DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP004Factor2577,
      nodeJet2N02704MinusPointP004Error2577, rounding2542,
      nodeJet2N02704MinusPointP004Radius2577]

theorem nodeJet2N02704MinusPointP004DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP004Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP004RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP004Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP004Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP004Rounded2577]

def nodeJet2N02704MinusPointP005Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP005Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02704MinusPointP005RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP005Factor2577
        nodeJet2N02704MinusPointP005Center2577) =
        nodeJet2N02704MinusPointP005Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP005RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP005Rounded2577‖ ≤
          nodeJet2N02704MinusPointP005Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP005Factor2577
      nodeJet2N02704MinusPointP005Center2577)
  rw [nodeJet2N02704MinusPointP005RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP005Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP005Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP005Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP005DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP005Factor2577,
      nodeJet2N02704MinusPointP005Error2577, rounding2542,
      nodeJet2N02704MinusPointP005Radius2577]

theorem nodeJet2N02704MinusPointP005DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP005Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP005RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP005Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP005Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP005Rounded2577]

def nodeJet2N02704MinusPointP006Rounded2577 : RatPair2542 :=
  (((119 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP006Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP006RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP006Factor2577
        nodeJet2N02704MinusPointP006Center2577) =
        nodeJet2N02704MinusPointP006Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP006RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP006Rounded2577‖ ≤
          nodeJet2N02704MinusPointP006Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP006Factor2577
      nodeJet2N02704MinusPointP006Center2577)
  rw [nodeJet2N02704MinusPointP006RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP006Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP006Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP006Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP006DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP006Factor2577,
      nodeJet2N02704MinusPointP006Error2577, rounding2542,
      nodeJet2N02704MinusPointP006Radius2577]

theorem nodeJet2N02704MinusPointP006DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP006Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP006RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP006Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP006Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP006Rounded2577]

def nodeJet2N02704MinusPointP007Rounded2577 : RatPair2542 :=
  (((37211707720505 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP007Radius2577 : ℝ := ((1102084581245 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704MinusPointP007RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP007Factor2577
        nodeJet2N02704MinusPointP007Center2577) =
        nodeJet2N02704MinusPointP007Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP007RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP007Rounded2577‖ ≤
          nodeJet2N02704MinusPointP007Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP007Factor2577
      nodeJet2N02704MinusPointP007Center2577)
  rw [nodeJet2N02704MinusPointP007RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP007Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP007Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP007Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP007DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP007Factor2577,
      nodeJet2N02704MinusPointP007Error2577, rounding2542,
      nodeJet2N02704MinusPointP007Radius2577]

theorem nodeJet2N02704MinusPointP007DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP007Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP007RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP007Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP007Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP007Rounded2577]

def nodeJet2N02704MinusPointP008Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP008Radius2577 : ℝ := ((2199029246697 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP008RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP008Factor2577
        nodeJet2N02704MinusPointP008Center2577) =
        nodeJet2N02704MinusPointP008Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP008RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP008Rounded2577‖ ≤
          nodeJet2N02704MinusPointP008Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP008Factor2577
      nodeJet2N02704MinusPointP008Center2577)
  rw [nodeJet2N02704MinusPointP008RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP008Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP008Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP008Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP008DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP008Factor2577,
      nodeJet2N02704MinusPointP008Error2577, rounding2542,
      nodeJet2N02704MinusPointP008Radius2577]

theorem nodeJet2N02704MinusPointP008DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP008Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP008RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP008Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP008Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP008Rounded2577]

def nodeJet2N02704MinusPointP009Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP009Radius2577 : ℝ := ((274878655843 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem nodeJet2N02704MinusPointP009RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP009Factor2577
        nodeJet2N02704MinusPointP009Center2577) =
        nodeJet2N02704MinusPointP009Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP009RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP009Rounded2577‖ ≤
          nodeJet2N02704MinusPointP009Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP009Factor2577
      nodeJet2N02704MinusPointP009Center2577)
  rw [nodeJet2N02704MinusPointP009RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP009Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP009Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP009Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP009DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP009Factor2577,
      nodeJet2N02704MinusPointP009Error2577, rounding2542,
      nodeJet2N02704MinusPointP009Radius2577]

theorem nodeJet2N02704MinusPointP009DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP009Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP009RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP009Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP009Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP009Rounded2577]

def nodeJet2N02704MinusPointP010Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP010Radius2577 : ℝ := ((2199029246771 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP010RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP010Factor2577
        nodeJet2N02704MinusPointP010Center2577) =
        nodeJet2N02704MinusPointP010Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP010RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP010Rounded2577‖ ≤
          nodeJet2N02704MinusPointP010Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP010Factor2577
      nodeJet2N02704MinusPointP010Center2577)
  rw [nodeJet2N02704MinusPointP010RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP010Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP010Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP010Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP010DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP010Factor2577,
      nodeJet2N02704MinusPointP010Error2577, rounding2542,
      nodeJet2N02704MinusPointP010Radius2577]

theorem nodeJet2N02704MinusPointP010DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP010Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP010RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP010Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP010Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP010Rounded2577]

def nodeJet2N02704MinusPointP011Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP011Radius2577 : ℝ := ((2199029246789 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP011RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP011Factor2577
        nodeJet2N02704MinusPointP011Center2577) =
        nodeJet2N02704MinusPointP011Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP011RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP011Rounded2577‖ ≤
          nodeJet2N02704MinusPointP011Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP011Factor2577
      nodeJet2N02704MinusPointP011Center2577)
  rw [nodeJet2N02704MinusPointP011RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP011Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP011Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP011Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP011DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP011Factor2577,
      nodeJet2N02704MinusPointP011Error2577, rounding2542,
      nodeJet2N02704MinusPointP011Radius2577]

theorem nodeJet2N02704MinusPointP011DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP011Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP011RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP011Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP011Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP011Rounded2577]

def nodeJet2N02704MinusPointP012Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP012Radius2577 : ℝ := ((2199029246807 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP012RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP012Factor2577
        nodeJet2N02704MinusPointP012Center2577) =
        nodeJet2N02704MinusPointP012Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP012RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP012Rounded2577‖ ≤
          nodeJet2N02704MinusPointP012Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP012Factor2577
      nodeJet2N02704MinusPointP012Center2577)
  rw [nodeJet2N02704MinusPointP012RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP012Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP012Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP012Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP012DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP012Factor2577,
      nodeJet2N02704MinusPointP012Error2577, rounding2542,
      nodeJet2N02704MinusPointP012Radius2577]

theorem nodeJet2N02704MinusPointP012DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP012Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP012RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP012Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP012Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP012Rounded2577]

def nodeJet2N02704MinusPointP013Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP013Radius2577 : ℝ := ((274878655853 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem nodeJet2N02704MinusPointP013RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP013Factor2577
        nodeJet2N02704MinusPointP013Center2577) =
        nodeJet2N02704MinusPointP013Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP013RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP013Rounded2577‖ ≤
          nodeJet2N02704MinusPointP013Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP013Factor2577
      nodeJet2N02704MinusPointP013Center2577)
  rw [nodeJet2N02704MinusPointP013RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP013Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP013Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP013Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP013DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP013Factor2577,
      nodeJet2N02704MinusPointP013Error2577, rounding2542,
      nodeJet2N02704MinusPointP013Radius2577]

theorem nodeJet2N02704MinusPointP013DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP013Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP013RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP013Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP013Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP013Rounded2577]

def nodeJet2N02704MinusPointP014Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP014Radius2577 : ℝ := ((274878655857 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem nodeJet2N02704MinusPointP014RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP014Factor2577
        nodeJet2N02704MinusPointP014Center2577) =
        nodeJet2N02704MinusPointP014Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP014RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP014Rounded2577‖ ≤
          nodeJet2N02704MinusPointP014Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP014Factor2577
      nodeJet2N02704MinusPointP014Center2577)
  rw [nodeJet2N02704MinusPointP014RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP014Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP014Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP014Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP014DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP014Factor2577,
      nodeJet2N02704MinusPointP014Error2577, rounding2542,
      nodeJet2N02704MinusPointP014Radius2577]

theorem nodeJet2N02704MinusPointP014DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP014Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP014RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP014Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP014Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP014Rounded2577]

def nodeJet2N02704MinusPointP015Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP015Radius2577 : ℝ := ((1099514623439 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704MinusPointP015RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP015Factor2577
        nodeJet2N02704MinusPointP015Center2577) =
        nodeJet2N02704MinusPointP015Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP015RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP015Rounded2577‖ ≤
          nodeJet2N02704MinusPointP015Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP015Factor2577
      nodeJet2N02704MinusPointP015Center2577)
  rw [nodeJet2N02704MinusPointP015RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP015Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP015Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP015Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP015DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP015Factor2577,
      nodeJet2N02704MinusPointP015Error2577, rounding2542,
      nodeJet2N02704MinusPointP015Radius2577]

theorem nodeJet2N02704MinusPointP015DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP015Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP015RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP015Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP015Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP015Rounded2577]

def nodeJet2N02704MinusPointP016Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP016Radius2577 : ℝ := ((2199029246895 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP016RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP016Factor2577
        nodeJet2N02704MinusPointP016Center2577) =
        nodeJet2N02704MinusPointP016Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP016RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP016Rounded2577‖ ≤
          nodeJet2N02704MinusPointP016Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP016Factor2577
      nodeJet2N02704MinusPointP016Center2577)
  rw [nodeJet2N02704MinusPointP016RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP016Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP016Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP016Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP016DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP016Factor2577,
      nodeJet2N02704MinusPointP016Error2577, rounding2542,
      nodeJet2N02704MinusPointP016Radius2577]

theorem nodeJet2N02704MinusPointP016DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP016Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP016RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP016Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP016Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP016Rounded2577]

def nodeJet2N02704MinusPointP017Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP017Radius2577 : ℝ := ((1099514623463 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704MinusPointP017RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP017Factor2577
        nodeJet2N02704MinusPointP017Center2577) =
        nodeJet2N02704MinusPointP017Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP017RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP017Rounded2577‖ ≤
          nodeJet2N02704MinusPointP017Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP017Factor2577
      nodeJet2N02704MinusPointP017Center2577)
  rw [nodeJet2N02704MinusPointP017RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP017Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP017Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP017Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP017DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP017Factor2577,
      nodeJet2N02704MinusPointP017Error2577, rounding2542,
      nodeJet2N02704MinusPointP017Radius2577]

theorem nodeJet2N02704MinusPointP017DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP017Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP017RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP017Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP017Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP017Rounded2577]

def nodeJet2N02704MinusPointP018Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP018Radius2577 : ℝ := ((1099514623469 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704MinusPointP018RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP018Factor2577
        nodeJet2N02704MinusPointP018Center2577) =
        nodeJet2N02704MinusPointP018Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP018RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP018Rounded2577‖ ≤
          nodeJet2N02704MinusPointP018Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP018Factor2577
      nodeJet2N02704MinusPointP018Center2577)
  rw [nodeJet2N02704MinusPointP018RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP018Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP018Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP018Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP018DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP018Factor2577,
      nodeJet2N02704MinusPointP018Error2577, rounding2542,
      nodeJet2N02704MinusPointP018Radius2577]

theorem nodeJet2N02704MinusPointP018DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP018Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP018RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP018Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP018Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP018Rounded2577]

def nodeJet2N02704MinusPointP019Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP019Radius2577 : ℝ := ((137439327935 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem nodeJet2N02704MinusPointP019RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP019Factor2577
        nodeJet2N02704MinusPointP019Center2577) =
        nodeJet2N02704MinusPointP019Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP019RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP019Rounded2577‖ ≤
          nodeJet2N02704MinusPointP019Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP019Factor2577
      nodeJet2N02704MinusPointP019Center2577)
  rw [nodeJet2N02704MinusPointP019RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP019Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP019Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP019Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP019DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP019Factor2577,
      nodeJet2N02704MinusPointP019Error2577, rounding2542,
      nodeJet2N02704MinusPointP019Radius2577]

theorem nodeJet2N02704MinusPointP019DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP019Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP019RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP019Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP019Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP019Rounded2577]

def nodeJet2N02704MinusPointP020Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP020Radius2577 : ℝ := ((2199029246983 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP020RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP020Factor2577
        nodeJet2N02704MinusPointP020Center2577) =
        nodeJet2N02704MinusPointP020Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP020RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP020Rounded2577‖ ≤
          nodeJet2N02704MinusPointP020Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP020Factor2577
      nodeJet2N02704MinusPointP020Center2577)
  rw [nodeJet2N02704MinusPointP020RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP020Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP020Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP020Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP020DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP020Factor2577,
      nodeJet2N02704MinusPointP020Error2577, rounding2542,
      nodeJet2N02704MinusPointP020Radius2577]

theorem nodeJet2N02704MinusPointP020DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP020Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP020RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP020Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP020Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP020Rounded2577]

def nodeJet2N02704MinusPointP021Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP021Radius2577 : ℝ := ((2199029247003 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP021RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP021Factor2577
        nodeJet2N02704MinusPointP021Center2577) =
        nodeJet2N02704MinusPointP021Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP021RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP021Rounded2577‖ ≤
          nodeJet2N02704MinusPointP021Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP021Factor2577
      nodeJet2N02704MinusPointP021Center2577)
  rw [nodeJet2N02704MinusPointP021RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP021Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP021Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP021Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP021DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP021Factor2577,
      nodeJet2N02704MinusPointP021Error2577, rounding2542,
      nodeJet2N02704MinusPointP021Radius2577]

theorem nodeJet2N02704MinusPointP021DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP021Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP021RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP021Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP021Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP021Rounded2577]

def nodeJet2N02704MinusPointP022Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP022Radius2577 : ℝ := ((2199029247013 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP022RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP022Factor2577
        nodeJet2N02704MinusPointP022Center2577) =
        nodeJet2N02704MinusPointP022Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP022RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP022Rounded2577‖ ≤
          nodeJet2N02704MinusPointP022Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP022Factor2577
      nodeJet2N02704MinusPointP022Center2577)
  rw [nodeJet2N02704MinusPointP022RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP022Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP022Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP022Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP022DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP022Factor2577,
      nodeJet2N02704MinusPointP022Error2577, rounding2542,
      nodeJet2N02704MinusPointP022Radius2577]

theorem nodeJet2N02704MinusPointP022DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP022Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP022RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP022Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP022Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP022Rounded2577]

def nodeJet2N02704MinusPointP023Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP023Radius2577 : ℝ := ((1099514623521 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704MinusPointP023RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP023Factor2577
        nodeJet2N02704MinusPointP023Center2577) =
        nodeJet2N02704MinusPointP023Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP023RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP023Rounded2577‖ ≤
          nodeJet2N02704MinusPointP023Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP023Factor2577
      nodeJet2N02704MinusPointP023Center2577)
  rw [nodeJet2N02704MinusPointP023RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP023Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP023Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP023Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP023DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP023Factor2577,
      nodeJet2N02704MinusPointP023Error2577, rounding2542,
      nodeJet2N02704MinusPointP023Radius2577]

theorem nodeJet2N02704MinusPointP023DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP023Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP023RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP023Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP023Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP023Rounded2577]

def nodeJet2N02704MinusPointP024Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP024Radius2577 : ℝ := ((2199029247055 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP024RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP024Factor2577
        nodeJet2N02704MinusPointP024Center2577) =
        nodeJet2N02704MinusPointP024Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP024RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP024Rounded2577‖ ≤
          nodeJet2N02704MinusPointP024Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP024Factor2577
      nodeJet2N02704MinusPointP024Center2577)
  rw [nodeJet2N02704MinusPointP024RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP024Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP024Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP024Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP024DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP024Factor2577,
      nodeJet2N02704MinusPointP024Error2577, rounding2542,
      nodeJet2N02704MinusPointP024Radius2577]

theorem nodeJet2N02704MinusPointP024DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP024Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP024RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP024Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP024Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP024Rounded2577]

def nodeJet2N02704MinusPointP025Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP025Radius2577 : ℝ := ((68719663971 : ℝ) /
        (4 * 10^40
        + 3556142965880123323311949751266331066368))

theorem nodeJet2N02704MinusPointP025RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP025Factor2577
        nodeJet2N02704MinusPointP025Center2577) =
        nodeJet2N02704MinusPointP025Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP025RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP025Rounded2577‖ ≤
          nodeJet2N02704MinusPointP025Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP025Factor2577
      nodeJet2N02704MinusPointP025Center2577)
  rw [nodeJet2N02704MinusPointP025RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP025Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP025Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP025Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP025DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP025Factor2577,
      nodeJet2N02704MinusPointP025Error2577, rounding2542,
      nodeJet2N02704MinusPointP025Radius2577]

theorem nodeJet2N02704MinusPointP025DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP025Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP025RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP025Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP025Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP025Rounded2577]

def nodeJet2N02704MinusPointP026Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP026Radius2577 : ℝ := ((2199029247089 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP026RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP026Factor2577
        nodeJet2N02704MinusPointP026Center2577) =
        nodeJet2N02704MinusPointP026Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP026RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP026Rounded2577‖ ≤
          nodeJet2N02704MinusPointP026Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP026Factor2577
      nodeJet2N02704MinusPointP026Center2577)
  rw [nodeJet2N02704MinusPointP026RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP026Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP026Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP026Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP026DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP026Factor2577,
      nodeJet2N02704MinusPointP026Error2577, rounding2542,
      nodeJet2N02704MinusPointP026Radius2577]

theorem nodeJet2N02704MinusPointP026DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP026Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP026RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP026Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP026Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP026Rounded2577]

def nodeJet2N02704MinusPointP027Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP027Radius2577 : ℝ := ((2199029247113 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP027RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP027Factor2577
        nodeJet2N02704MinusPointP027Center2577) =
        nodeJet2N02704MinusPointP027Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP027RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP027Rounded2577‖ ≤
          nodeJet2N02704MinusPointP027Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP027Factor2577
      nodeJet2N02704MinusPointP027Center2577)
  rw [nodeJet2N02704MinusPointP027RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP027Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP027Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP027Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP027DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP027Factor2577,
      nodeJet2N02704MinusPointP027Error2577, rounding2542,
      nodeJet2N02704MinusPointP027Radius2577]

theorem nodeJet2N02704MinusPointP027DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP027Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP027RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP027Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP027Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP027Rounded2577]

def nodeJet2N02704MinusPointP028Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP028Radius2577 : ℝ := ((2199029247123 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704MinusPointP028RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP028Factor2577
        nodeJet2N02704MinusPointP028Center2577) =
        nodeJet2N02704MinusPointP028Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP028RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP028Rounded2577‖ ≤
          nodeJet2N02704MinusPointP028Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP028Factor2577
      nodeJet2N02704MinusPointP028Center2577)
  rw [nodeJet2N02704MinusPointP028RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP028Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP028Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP028Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP028DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP028Factor2577,
      nodeJet2N02704MinusPointP028Error2577, rounding2542,
      nodeJet2N02704MinusPointP028Radius2577]

theorem nodeJet2N02704MinusPointP028DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP028Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP028RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP028Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP028Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP028Rounded2577]

def nodeJet2N02704MinusPointP029Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704MinusPointP029Radius2577 : ℝ := ((1099514623569 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704MinusPointP029RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704MinusPointP029Factor2577
        nodeJet2N02704MinusPointP029Center2577) =
        nodeJet2N02704MinusPointP029Rounded2577 := by
  cbv

theorem nodeJet2N02704MinusPointP029RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02704MinusPointPosition2577 -
      embedPair2542 nodeJet2N02704MinusPointP029Rounded2577‖ ≤
          nodeJet2N02704MinusPointP029Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704MinusPointP029Factor2577
      nodeJet2N02704MinusPointP029Center2577)
  rw [nodeJet2N02704MinusPointP029RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP029Factor2577 * embedPair2542
        nodeJet2N02704MinusPointP029Center2577)
    (embedPair2542 nodeJet2N02704MinusPointP029Rounded2577)).trans (add_le_add
        nodeJet2N02704MinusPointP029DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704MinusPointP029Factor2577,
      nodeJet2N02704MinusPointP029Error2577, rounding2542,
      nodeJet2N02704MinusPointP029Radius2577]

theorem nodeJet2N02704MinusPointP029DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02704MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02704MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02704MinusPointPosition2577)
    (embedPair2542 nodeJet2N02704MinusPointP029Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704MinusPointP029RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704MinusPointP029Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704MinusPointP029Radius2577, pairMagnitude2542,
      nodeJet2N02704MinusPointP029Rounded2577]

noncomputable def nodeJet2N02704MinusSignedValue2577 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 nodeJet2N02704MinusPointP000Rounded2577
  | 1 => embedPair2542 nodeJet2N02704MinusPointP001Rounded2577
  | 2 => embedPair2542 nodeJet2N02704MinusPointP002Rounded2577
  | 3 => embedPair2542 nodeJet2N02704MinusPointP003Rounded2577
  | 4 => embedPair2542 nodeJet2N02704MinusPointP004Rounded2577
  | 5 => embedPair2542 nodeJet2N02704MinusPointP005Rounded2577
  | 6 => embedPair2542 nodeJet2N02704MinusPointP006Rounded2577
  | 7 => embedPair2542 nodeJet2N02704MinusPointP007Rounded2577
  | 8 => embedPair2542 nodeJet2N02704MinusPointP008Rounded2577
  | 9 => embedPair2542 nodeJet2N02704MinusPointP009Rounded2577
  | 10 => embedPair2542 nodeJet2N02704MinusPointP010Rounded2577
  | 11 => embedPair2542 nodeJet2N02704MinusPointP011Rounded2577
  | 12 => embedPair2542 nodeJet2N02704MinusPointP012Rounded2577
  | 13 => embedPair2542 nodeJet2N02704MinusPointP013Rounded2577
  | 14 => embedPair2542 nodeJet2N02704MinusPointP014Rounded2577
  | 15 => embedPair2542 nodeJet2N02704MinusPointP015Rounded2577
  | 16 => embedPair2542 nodeJet2N02704MinusPointP016Rounded2577
  | 17 => embedPair2542 nodeJet2N02704MinusPointP017Rounded2577
  | 18 => embedPair2542 nodeJet2N02704MinusPointP018Rounded2577
  | 19 => embedPair2542 nodeJet2N02704MinusPointP019Rounded2577
  | 20 => embedPair2542 nodeJet2N02704MinusPointP020Rounded2577
  | 21 => embedPair2542 nodeJet2N02704MinusPointP021Rounded2577
  | 22 => embedPair2542 nodeJet2N02704MinusPointP022Rounded2577
  | 23 => embedPair2542 nodeJet2N02704MinusPointP023Rounded2577
  | 24 => embedPair2542 nodeJet2N02704MinusPointP024Rounded2577
  | 25 => embedPair2542 nodeJet2N02704MinusPointP025Rounded2577
  | 26 => embedPair2542 nodeJet2N02704MinusPointP026Rounded2577
  | 27 => embedPair2542 nodeJet2N02704MinusPointP027Rounded2577
  | 28 => embedPair2542 nodeJet2N02704MinusPointP028Rounded2577
  | 29 => embedPair2542 nodeJet2N02704MinusPointP029Rounded2577
  | _ => 0

noncomputable def nodeJet2N02704MinusSignedError2577 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => nodeJet2N02704MinusPointP000Radius2577
  | 1 => nodeJet2N02704MinusPointP001Radius2577
  | 2 => nodeJet2N02704MinusPointP002Radius2577
  | 3 => nodeJet2N02704MinusPointP003Radius2577
  | 4 => nodeJet2N02704MinusPointP004Radius2577
  | 5 => nodeJet2N02704MinusPointP005Radius2577
  | 6 => nodeJet2N02704MinusPointP006Radius2577
  | 7 => nodeJet2N02704MinusPointP007Radius2577
  | 8 => nodeJet2N02704MinusPointP008Radius2577
  | 9 => nodeJet2N02704MinusPointP009Radius2577
  | 10 => nodeJet2N02704MinusPointP010Radius2577
  | 11 => nodeJet2N02704MinusPointP011Radius2577
  | 12 => nodeJet2N02704MinusPointP012Radius2577
  | 13 => nodeJet2N02704MinusPointP013Radius2577
  | 14 => nodeJet2N02704MinusPointP014Radius2577
  | 15 => nodeJet2N02704MinusPointP015Radius2577
  | 16 => nodeJet2N02704MinusPointP016Radius2577
  | 17 => nodeJet2N02704MinusPointP017Radius2577
  | 18 => nodeJet2N02704MinusPointP018Radius2577
  | 19 => nodeJet2N02704MinusPointP019Radius2577
  | 20 => nodeJet2N02704MinusPointP020Radius2577
  | 21 => nodeJet2N02704MinusPointP021Radius2577
  | 22 => nodeJet2N02704MinusPointP022Radius2577
  | 23 => nodeJet2N02704MinusPointP023Radius2577
  | 24 => nodeJet2N02704MinusPointP024Radius2577
  | 25 => nodeJet2N02704MinusPointP025Radius2577
  | 26 => nodeJet2N02704MinusPointP026Radius2577
  | 27 => nodeJet2N02704MinusPointP027Radius2577
  | 28 => nodeJet2N02704MinusPointP028Radius2577
  | 29 => nodeJet2N02704MinusPointP029Radius2577
  | _ => 0

theorem nodeJet2N02704MinusSignedExpError2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02704MinusPointPosition2577 -
        nodeJet2N02704MinusSignedValue2577 i‖ ≤ nodeJet2N02704MinusSignedError2577 i := by
  fin_cases i
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP000RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP001RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP002RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP003RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP004RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP005RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP006RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP007RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP008RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP009RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP010RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP011RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP012RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP013RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP014RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP015RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP016RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP017RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP018RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP019RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP020RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP021RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP022RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP023RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP024RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP025RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP026RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP027RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP028RoundedError2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP029RoundedError2577

theorem nodeJet2N02704MinusSignedUnitNorm2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02704MinusPointPosition2577‖ ≤ 1
        := by
  fin_cases i
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP000DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP001DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP002DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP003DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP004DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP005DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP006DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP007DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP008DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP009DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP010DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP011DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP012DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP013DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP014DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP015DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP016DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP017DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP018DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP019DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP020DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP021DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP022DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP023DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP024DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP025DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP026DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP027DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP028DerivativeNorm2577
  · simpa only [nodeJet2N02704MinusSignedValue2577, nodeJet2N02704MinusSignedError2577] using
      nodeJet2N02704MinusPointP029DerivativeNorm2577

noncomputable def nodeJet2N02704MinusSignedSum2577 : ℂ := ⟨(((-(((7734557955095 * 10^40
        + 7376914538239901575182111630633406032256) * 10^40
        + 2623516640654896307041808279284099044613) * 10^40
        + 44732873917307207269045309694343355835)) : ℝ) /
        (((354901720847 * 10^40
        + 4643020260370155703147140398639456481045) * 10^40
        + 2162182138631867152739912007974911672398) * 10^40
        + 1329865996466075003059657194108692201472)),
    (((((2247297733310 * 10^40
        + 1313258238131858443475725920497542831608) * 10^40
        + 8191796870404375652677955207449387034817) * 10^40
        + 2651378853593729497509417860270050986151) : ℝ) /
        (((177450860423 * 10^40
        + 7321510130185077851573570199319728240522) * 10^40
        + 6081091069315933576369956003987455836199) * 10^40
        + 664932998233037501529828597054346100736))⟩

noncomputable def nodeJet2N02704MinusSignedUpper2577 : ℝ := ((1260300569 : ℝ) /
        50000000)

theorem nodeJet2N02704MinusSignedSum_eq2577 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02704MinusSignedValue2577 i) =
      nodeJet2N02704MinusSignedSum2577 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        nodeJet2N02704MinusSignedValue2577,
      nodeJet2N02704MinusSignedSum2577, embedPair2542, nodeJet2N02704MinusPointP000Rounded2577,
      nodeJet2N02704MinusPointP001Rounded2577,
      nodeJet2N02704MinusPointP002Rounded2577,
      nodeJet2N02704MinusPointP003Rounded2577,
      nodeJet2N02704MinusPointP004Rounded2577,
      nodeJet2N02704MinusPointP005Rounded2577,
      nodeJet2N02704MinusPointP006Rounded2577,
      nodeJet2N02704MinusPointP007Rounded2577,
      nodeJet2N02704MinusPointP008Rounded2577,
      nodeJet2N02704MinusPointP009Rounded2577,
      nodeJet2N02704MinusPointP010Rounded2577,
      nodeJet2N02704MinusPointP011Rounded2577,
      nodeJet2N02704MinusPointP012Rounded2577,
      nodeJet2N02704MinusPointP013Rounded2577,
      nodeJet2N02704MinusPointP014Rounded2577,
      nodeJet2N02704MinusPointP015Rounded2577,
      nodeJet2N02704MinusPointP016Rounded2577,
      nodeJet2N02704MinusPointP017Rounded2577,
      nodeJet2N02704MinusPointP018Rounded2577,
      nodeJet2N02704MinusPointP019Rounded2577,
      nodeJet2N02704MinusPointP020Rounded2577,
      nodeJet2N02704MinusPointP021Rounded2577,
      nodeJet2N02704MinusPointP022Rounded2577,
      nodeJet2N02704MinusPointP023Rounded2577,
      nodeJet2N02704MinusPointP024Rounded2577,
      nodeJet2N02704MinusPointP025Rounded2577,
      nodeJet2N02704MinusPointP026Rounded2577,
      nodeJet2N02704MinusPointP027Rounded2577,
      nodeJet2N02704MinusPointP028Rounded2577,
      nodeJet2N02704MinusPointP029Rounded2577, Complex.mul_re, Complex.mul_im]

theorem nodeJet2N02704MinusSignedSum_norm2577 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02704MinusSignedValue2577 i‖ ≤
        ((315075141 :
        ℝ) /
        12500000) := by
  rw [nodeJet2N02704MinusSignedSum_eq2577]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [nodeJet2N02704MinusSignedSum2577]

theorem nodeJet2N02704MinusSignedCharge2577 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02704MinusSignedError2577 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      nodeJet2N02704MinusSignedError2577, nodeJet2N02704MinusPointP000Radius2577,
      nodeJet2N02704MinusPointP001Radius2577,
      nodeJet2N02704MinusPointP002Radius2577,
      nodeJet2N02704MinusPointP003Radius2577,
      nodeJet2N02704MinusPointP004Radius2577,
      nodeJet2N02704MinusPointP005Radius2577,
      nodeJet2N02704MinusPointP006Radius2577,
      nodeJet2N02704MinusPointP007Radius2577,
      nodeJet2N02704MinusPointP008Radius2577,
      nodeJet2N02704MinusPointP009Radius2577,
      nodeJet2N02704MinusPointP010Radius2577,
      nodeJet2N02704MinusPointP011Radius2577,
      nodeJet2N02704MinusPointP012Radius2577,
      nodeJet2N02704MinusPointP013Radius2577,
      nodeJet2N02704MinusPointP014Radius2577,
      nodeJet2N02704MinusPointP015Radius2577,
      nodeJet2N02704MinusPointP016Radius2577,
      nodeJet2N02704MinusPointP017Radius2577,
      nodeJet2N02704MinusPointP018Radius2577,
      nodeJet2N02704MinusPointP019Radius2577,
      nodeJet2N02704MinusPointP020Radius2577,
      nodeJet2N02704MinusPointP021Radius2577,
      nodeJet2N02704MinusPointP022Radius2577,
      nodeJet2N02704MinusPointP023Radius2577,
      nodeJet2N02704MinusPointP024Radius2577,
      nodeJet2N02704MinusPointP025Radius2577,
      nodeJet2N02704MinusPointP026Radius2577,
      nodeJet2N02704MinusPointP027Radius2577,
      nodeJet2N02704MinusPointP028Radius2577,
      nodeJet2N02704MinusPointP029Radius2577]

theorem nodeJet2N02704MinusSignedUpper_le2577 :
    signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 nodeJet2N02704MinusPointPosition2577 ≤ nodeJet2N02704MinusSignedUpper2577
          := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02704MinusPointPosition2577‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02704MinusSignedValue2577 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02704MinusSignedError2577 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (nodeJet2N02704MinusSignedExpError2577
        i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02704MinusPointPosition2577‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (nodeJet2N02704MinusSignedUnitNorm2577 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02704MinusPointPosition2577‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 nodeJet2N02704MinusSignedUpper2577
  linarith [nodeJet2N02704MinusSignedSum_norm2577, nodeJet2N02704MinusSignedCharge2577]

theorem nodeJet2N02704MinusPhysical2577 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        nodeJet2N02704MinusPointPosition2577‖ ≤
      nodeJet2N02704MinusSignedUpper2577 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        nodeJet2N02704MinusPointPosition2577
  exact h.trans nodeJet2N02704MinusSignedUpper_le2577

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.nodeJet2N02704MinusSignedExpError2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02704MinusSignedSum_eq2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02704MinusSignedCharge2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02704MinusSignedUpper_le2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02704MinusPhysical2577
