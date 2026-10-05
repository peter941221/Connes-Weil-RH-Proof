import ConnesWeilRH.Dev.C1RouteANodeJet2N02705Minus2577
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem nodeJet2N02705MinusPoint_triangle2577 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def nodeJet2N02705MinusPointP000Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP000Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02705MinusPointP000RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP000Factor2577
        nodeJet2N02705MinusPointP000Center2577) =
        nodeJet2N02705MinusPointP000Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP000RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP000Rounded2577‖ ≤
          nodeJet2N02705MinusPointP000Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP000Factor2577
      nodeJet2N02705MinusPointP000Center2577)
  rw [nodeJet2N02705MinusPointP000RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP000Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP000Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP000Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP000DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP000Factor2577,
      nodeJet2N02705MinusPointP000Error2577, rounding2542,
      nodeJet2N02705MinusPointP000Radius2577]

theorem nodeJet2N02705MinusPointP000DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP000Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP000RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP000Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP000Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP000Rounded2577]

def nodeJet2N02705MinusPointP001Rounded2577 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP001Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705MinusPointP001RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP001Factor2577
        nodeJet2N02705MinusPointP001Center2577) =
        nodeJet2N02705MinusPointP001Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP001RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP001Rounded2577‖ ≤
          nodeJet2N02705MinusPointP001Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP001Factor2577
      nodeJet2N02705MinusPointP001Center2577)
  rw [nodeJet2N02705MinusPointP001RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP001Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP001Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP001Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP001DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP001Factor2577,
      nodeJet2N02705MinusPointP001Error2577, rounding2542,
      nodeJet2N02705MinusPointP001Radius2577]

theorem nodeJet2N02705MinusPointP001DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP001Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP001RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP001Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP001Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP001Rounded2577]

def nodeJet2N02705MinusPointP002Rounded2577 : RatPair2542 :=
  (((42365201 : ℚ) /
        1267650600228229401496703205376),
    (((-18127399) : ℚ) /
        1267650600228229401496703205376))

noncomputable def nodeJet2N02705MinusPointP002Radius2577 : ℝ := ((1099511715973 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705MinusPointP002RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP002Factor2577
        nodeJet2N02705MinusPointP002Center2577) =
        nodeJet2N02705MinusPointP002Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP002RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP002Rounded2577‖ ≤
          nodeJet2N02705MinusPointP002Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP002Factor2577
      nodeJet2N02705MinusPointP002Center2577)
  rw [nodeJet2N02705MinusPointP002RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP002Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP002Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP002Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP002DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP002Factor2577,
      nodeJet2N02705MinusPointP002Error2577, rounding2542,
      nodeJet2N02705MinusPointP002Radius2577]

theorem nodeJet2N02705MinusPointP002DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP002Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP002RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP002Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP002Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP002Rounded2577]

def nodeJet2N02705MinusPointP003Rounded2577 : RatPair2542 :=
  (((162951464377133 : ℚ) /
        633825300114114700748351602688),
    ((92381385411857 : ℚ) /
        633825300114114700748351602688))

noncomputable def nodeJet2N02705MinusPointP003Radius2577 : ℝ := ((4053620911593 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705MinusPointP003RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP003Factor2577
        nodeJet2N02705MinusPointP003Center2577) =
        nodeJet2N02705MinusPointP003Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP003RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP003Rounded2577‖ ≤
          nodeJet2N02705MinusPointP003Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP003Factor2577
      nodeJet2N02705MinusPointP003Center2577)
  rw [nodeJet2N02705MinusPointP003RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP003Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP003Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP003Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP003DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP003Factor2577,
      nodeJet2N02705MinusPointP003Error2577, rounding2542,
      nodeJet2N02705MinusPointP003Radius2577]

theorem nodeJet2N02705MinusPointP003DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP003Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP003RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP003Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP003Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP003Rounded2577]

def nodeJet2N02705MinusPointP004Rounded2577 : RatPair2542 :=
  (((109089474491868997 : ℚ) /
        1267650600228229401496703205376),
    (((-124344604546913865) : ℚ) /
        1267650600228229401496703205376))

noncomputable def nodeJet2N02705MinusPointP004Radius2577 : ℝ := ((363230339275087 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705MinusPointP004RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP004Factor2577
        nodeJet2N02705MinusPointP004Center2577) =
        nodeJet2N02705MinusPointP004Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP004RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP004Rounded2577‖ ≤
          nodeJet2N02705MinusPointP004Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP004Factor2577
      nodeJet2N02705MinusPointP004Center2577)
  rw [nodeJet2N02705MinusPointP004RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP004Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP004Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP004Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP004DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP004Factor2577,
      nodeJet2N02705MinusPointP004Error2577, rounding2542,
      nodeJet2N02705MinusPointP004Radius2577]

theorem nodeJet2N02705MinusPointP004DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP004Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP004RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP004Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP004Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP004Rounded2577]

def nodeJet2N02705MinusPointP005Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP005Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02705MinusPointP005RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP005Factor2577
        nodeJet2N02705MinusPointP005Center2577) =
        nodeJet2N02705MinusPointP005Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP005RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP005Rounded2577‖ ≤
          nodeJet2N02705MinusPointP005Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP005Factor2577
      nodeJet2N02705MinusPointP005Center2577)
  rw [nodeJet2N02705MinusPointP005RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP005Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP005Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP005Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP005DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP005Factor2577,
      nodeJet2N02705MinusPointP005Error2577, rounding2542,
      nodeJet2N02705MinusPointP005Radius2577]

theorem nodeJet2N02705MinusPointP005DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP005Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP005RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP005Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP005Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP005Rounded2577]

def nodeJet2N02705MinusPointP006Rounded2577 : RatPair2542 :=
  (((65 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP006Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705MinusPointP006RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP006Factor2577
        nodeJet2N02705MinusPointP006Center2577) =
        nodeJet2N02705MinusPointP006Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP006RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP006Rounded2577‖ ≤
          nodeJet2N02705MinusPointP006Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP006Factor2577
      nodeJet2N02705MinusPointP006Center2577)
  rw [nodeJet2N02705MinusPointP006RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP006Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP006Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP006Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP006DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP006Factor2577,
      nodeJet2N02705MinusPointP006Error2577, rounding2542,
      nodeJet2N02705MinusPointP006Radius2577]

theorem nodeJet2N02705MinusPointP006DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP006Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP006RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP006Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP006Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP006Rounded2577]

def nodeJet2N02705MinusPointP007Rounded2577 : RatPair2542 :=
  (((37774018175679 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP007Radius2577 : ℝ := ((2204245485137 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705MinusPointP007RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP007Factor2577
        nodeJet2N02705MinusPointP007Center2577) =
        nodeJet2N02705MinusPointP007Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP007RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP007Rounded2577‖ ≤
          nodeJet2N02705MinusPointP007Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP007Factor2577
      nodeJet2N02705MinusPointP007Center2577)
  rw [nodeJet2N02705MinusPointP007RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP007Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP007Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP007Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP007DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP007Factor2577,
      nodeJet2N02705MinusPointP007Error2577, rounding2542,
      nodeJet2N02705MinusPointP007Radius2577]

theorem nodeJet2N02705MinusPointP007DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP007Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP007RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP007Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP007Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP007Rounded2577]

def nodeJet2N02705MinusPointP008Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP008Radius2577 : ℝ := ((2199025709391 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705MinusPointP008RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP008Factor2577
        nodeJet2N02705MinusPointP008Center2577) =
        nodeJet2N02705MinusPointP008Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP008RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP008Rounded2577‖ ≤
          nodeJet2N02705MinusPointP008Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP008Factor2577
      nodeJet2N02705MinusPointP008Center2577)
  rw [nodeJet2N02705MinusPointP008RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP008Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP008Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP008Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP008DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP008Factor2577,
      nodeJet2N02705MinusPointP008Error2577, rounding2542,
      nodeJet2N02705MinusPointP008Radius2577]

theorem nodeJet2N02705MinusPointP008DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP008Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP008RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP008Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP008Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP008Rounded2577]

def nodeJet2N02705MinusPointP009Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP009Radius2577 : ℝ := ((2199025709421 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705MinusPointP009RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP009Factor2577
        nodeJet2N02705MinusPointP009Center2577) =
        nodeJet2N02705MinusPointP009Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP009RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP009Rounded2577‖ ≤
          nodeJet2N02705MinusPointP009Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP009Factor2577
      nodeJet2N02705MinusPointP009Center2577)
  rw [nodeJet2N02705MinusPointP009RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP009Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP009Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP009Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP009DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP009Factor2577,
      nodeJet2N02705MinusPointP009Error2577, rounding2542,
      nodeJet2N02705MinusPointP009Radius2577]

theorem nodeJet2N02705MinusPointP009DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP009Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP009RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP009Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP009Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP009Rounded2577]

def nodeJet2N02705MinusPointP010Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP010Radius2577 : ℝ := ((1099512854719 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705MinusPointP010RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP010Factor2577
        nodeJet2N02705MinusPointP010Center2577) =
        nodeJet2N02705MinusPointP010Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP010RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP010Rounded2577‖ ≤
          nodeJet2N02705MinusPointP010Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP010Factor2577
      nodeJet2N02705MinusPointP010Center2577)
  rw [nodeJet2N02705MinusPointP010RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP010Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP010Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP010Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP010DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP010Factor2577,
      nodeJet2N02705MinusPointP010Error2577, rounding2542,
      nodeJet2N02705MinusPointP010Radius2577]

theorem nodeJet2N02705MinusPointP010DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP010Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP010RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP010Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP010Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP010Rounded2577]

def nodeJet2N02705MinusPointP011Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP011Radius2577 : ℝ := ((1099512854725 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705MinusPointP011RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP011Factor2577
        nodeJet2N02705MinusPointP011Center2577) =
        nodeJet2N02705MinusPointP011Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP011RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP011Rounded2577‖ ≤
          nodeJet2N02705MinusPointP011Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP011Factor2577
      nodeJet2N02705MinusPointP011Center2577)
  rw [nodeJet2N02705MinusPointP011RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP011Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP011Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP011Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP011DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP011Factor2577,
      nodeJet2N02705MinusPointP011Error2577, rounding2542,
      nodeJet2N02705MinusPointP011Radius2577]

theorem nodeJet2N02705MinusPointP011DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP011Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP011RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP011Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP011Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP011Rounded2577]

def nodeJet2N02705MinusPointP012Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP012Radius2577 : ℝ := ((1099512854731 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705MinusPointP012RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP012Factor2577
        nodeJet2N02705MinusPointP012Center2577) =
        nodeJet2N02705MinusPointP012Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP012RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP012Rounded2577‖ ≤
          nodeJet2N02705MinusPointP012Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP012Factor2577
      nodeJet2N02705MinusPointP012Center2577)
  rw [nodeJet2N02705MinusPointP012RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP012Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP012Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP012Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP012DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP012Factor2577,
      nodeJet2N02705MinusPointP012Error2577, rounding2542,
      nodeJet2N02705MinusPointP012Radius2577]

theorem nodeJet2N02705MinusPointP012DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP012Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP012RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP012Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP012Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP012Rounded2577]

def nodeJet2N02705MinusPointP013Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP013Radius2577 : ℝ := ((2199025709473 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705MinusPointP013RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP013Factor2577
        nodeJet2N02705MinusPointP013Center2577) =
        nodeJet2N02705MinusPointP013Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP013RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP013Rounded2577‖ ≤
          nodeJet2N02705MinusPointP013Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP013Factor2577
      nodeJet2N02705MinusPointP013Center2577)
  rw [nodeJet2N02705MinusPointP013RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP013Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP013Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP013Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP013DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP013Factor2577,
      nodeJet2N02705MinusPointP013Error2577, rounding2542,
      nodeJet2N02705MinusPointP013Radius2577]

theorem nodeJet2N02705MinusPointP013DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP013Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP013RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP013Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP013Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP013Rounded2577]

def nodeJet2N02705MinusPointP014Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP014Radius2577 : ℝ := ((2199025709493 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705MinusPointP014RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP014Factor2577
        nodeJet2N02705MinusPointP014Center2577) =
        nodeJet2N02705MinusPointP014Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP014RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP014Rounded2577‖ ≤
          nodeJet2N02705MinusPointP014Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP014Factor2577
      nodeJet2N02705MinusPointP014Center2577)
  rw [nodeJet2N02705MinusPointP014RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP014Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP014Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP014Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP014DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP014Factor2577,
      nodeJet2N02705MinusPointP014Error2577, rounding2542,
      nodeJet2N02705MinusPointP014Radius2577]

theorem nodeJet2N02705MinusPointP014DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP014Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP014RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP014Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP014Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP014Rounded2577]

def nodeJet2N02705MinusPointP015Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP015Radius2577 : ℝ := ((2199025709507 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705MinusPointP015RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP015Factor2577
        nodeJet2N02705MinusPointP015Center2577) =
        nodeJet2N02705MinusPointP015Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP015RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP015Rounded2577‖ ≤
          nodeJet2N02705MinusPointP015Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP015Factor2577
      nodeJet2N02705MinusPointP015Center2577)
  rw [nodeJet2N02705MinusPointP015RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP015Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP015Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP015Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP015DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP015Factor2577,
      nodeJet2N02705MinusPointP015Error2577, rounding2542,
      nodeJet2N02705MinusPointP015Radius2577]

theorem nodeJet2N02705MinusPointP015DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP015Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP015RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP015Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP015Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP015Rounded2577]

def nodeJet2N02705MinusPointP016Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP016Radius2577 : ℝ := ((1099512854759 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705MinusPointP016RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP016Factor2577
        nodeJet2N02705MinusPointP016Center2577) =
        nodeJet2N02705MinusPointP016Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP016RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP016Rounded2577‖ ≤
          nodeJet2N02705MinusPointP016Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP016Factor2577
      nodeJet2N02705MinusPointP016Center2577)
  rw [nodeJet2N02705MinusPointP016RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP016Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP016Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP016Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP016DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP016Factor2577,
      nodeJet2N02705MinusPointP016Error2577, rounding2542,
      nodeJet2N02705MinusPointP016Radius2577]

theorem nodeJet2N02705MinusPointP016DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP016Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP016RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP016Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP016Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP016Rounded2577]

def nodeJet2N02705MinusPointP017Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP017Radius2577 : ℝ := ((1099512854769 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705MinusPointP017RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP017Factor2577
        nodeJet2N02705MinusPointP017Center2577) =
        nodeJet2N02705MinusPointP017Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP017RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP017Rounded2577‖ ≤
          nodeJet2N02705MinusPointP017Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP017Factor2577
      nodeJet2N02705MinusPointP017Center2577)
  rw [nodeJet2N02705MinusPointP017RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP017Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP017Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP017Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP017DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP017Factor2577,
      nodeJet2N02705MinusPointP017Error2577, rounding2542,
      nodeJet2N02705MinusPointP017Radius2577]

theorem nodeJet2N02705MinusPointP017DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP017Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP017RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP017Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP017Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP017Rounded2577]

def nodeJet2N02705MinusPointP018Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP018Radius2577 : ℝ := ((1099512854773 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705MinusPointP018RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP018Factor2577
        nodeJet2N02705MinusPointP018Center2577) =
        nodeJet2N02705MinusPointP018Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP018RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP018Rounded2577‖ ≤
          nodeJet2N02705MinusPointP018Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP018Factor2577
      nodeJet2N02705MinusPointP018Center2577)
  rw [nodeJet2N02705MinusPointP018RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP018Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP018Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP018Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP018DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP018Factor2577,
      nodeJet2N02705MinusPointP018Error2577, rounding2542,
      nodeJet2N02705MinusPointP018Radius2577]

theorem nodeJet2N02705MinusPointP018DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP018Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP018RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP018Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP018Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP018Rounded2577]

def nodeJet2N02705MinusPointP019Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP019Radius2577 : ℝ := ((2199025709559 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705MinusPointP019RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP019Factor2577
        nodeJet2N02705MinusPointP019Center2577) =
        nodeJet2N02705MinusPointP019Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP019RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP019Rounded2577‖ ≤
          nodeJet2N02705MinusPointP019Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP019Factor2577
      nodeJet2N02705MinusPointP019Center2577)
  rw [nodeJet2N02705MinusPointP019RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP019Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP019Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP019Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP019DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP019Factor2577,
      nodeJet2N02705MinusPointP019Error2577, rounding2542,
      nodeJet2N02705MinusPointP019Radius2577]

theorem nodeJet2N02705MinusPointP019DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP019Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP019RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP019Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP019Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP019Rounded2577]

def nodeJet2N02705MinusPointP020Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP020Radius2577 : ℝ := ((1099512854787 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705MinusPointP020RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP020Factor2577
        nodeJet2N02705MinusPointP020Center2577) =
        nodeJet2N02705MinusPointP020Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP020RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP020Rounded2577‖ ≤
          nodeJet2N02705MinusPointP020Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP020Factor2577
      nodeJet2N02705MinusPointP020Center2577)
  rw [nodeJet2N02705MinusPointP020RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP020Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP020Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP020Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP020DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP020Factor2577,
      nodeJet2N02705MinusPointP020Error2577, rounding2542,
      nodeJet2N02705MinusPointP020Radius2577]

theorem nodeJet2N02705MinusPointP020DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP020Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP020RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP020Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP020Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP020Rounded2577]

def nodeJet2N02705MinusPointP021Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP021Radius2577 : ℝ := ((2199025709587 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705MinusPointP021RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP021Factor2577
        nodeJet2N02705MinusPointP021Center2577) =
        nodeJet2N02705MinusPointP021Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP021RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP021Rounded2577‖ ≤
          nodeJet2N02705MinusPointP021Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP021Factor2577
      nodeJet2N02705MinusPointP021Center2577)
  rw [nodeJet2N02705MinusPointP021RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP021Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP021Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP021Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP021DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP021Factor2577,
      nodeJet2N02705MinusPointP021Error2577, rounding2542,
      nodeJet2N02705MinusPointP021Radius2577]

theorem nodeJet2N02705MinusPointP021DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP021Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP021RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP021Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP021Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP021Rounded2577]

def nodeJet2N02705MinusPointP022Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP022Radius2577 : ℝ := ((2199025709593 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705MinusPointP022RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP022Factor2577
        nodeJet2N02705MinusPointP022Center2577) =
        nodeJet2N02705MinusPointP022Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP022RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP022Rounded2577‖ ≤
          nodeJet2N02705MinusPointP022Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP022Factor2577
      nodeJet2N02705MinusPointP022Center2577)
  rw [nodeJet2N02705MinusPointP022RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP022Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP022Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP022Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP022DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP022Factor2577,
      nodeJet2N02705MinusPointP022Error2577, rounding2542,
      nodeJet2N02705MinusPointP022Radius2577]

theorem nodeJet2N02705MinusPointP022DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP022Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP022RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP022Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP022Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP022Rounded2577]

def nodeJet2N02705MinusPointP023Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP023Radius2577 : ℝ := ((549756427403 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02705MinusPointP023RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP023Factor2577
        nodeJet2N02705MinusPointP023Center2577) =
        nodeJet2N02705MinusPointP023Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP023RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP023Rounded2577‖ ≤
          nodeJet2N02705MinusPointP023Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP023Factor2577
      nodeJet2N02705MinusPointP023Center2577)
  rw [nodeJet2N02705MinusPointP023RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP023Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP023Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP023Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP023DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP023Factor2577,
      nodeJet2N02705MinusPointP023Error2577, rounding2542,
      nodeJet2N02705MinusPointP023Radius2577]

theorem nodeJet2N02705MinusPointP023DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP023Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP023RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP023Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP023Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP023Rounded2577]

def nodeJet2N02705MinusPointP024Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP024Radius2577 : ℝ := ((549756427405 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02705MinusPointP024RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP024Factor2577
        nodeJet2N02705MinusPointP024Center2577) =
        nodeJet2N02705MinusPointP024Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP024RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP024Rounded2577‖ ≤
          nodeJet2N02705MinusPointP024Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP024Factor2577
      nodeJet2N02705MinusPointP024Center2577)
  rw [nodeJet2N02705MinusPointP024RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP024Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP024Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP024Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP024DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP024Factor2577,
      nodeJet2N02705MinusPointP024Error2577, rounding2542,
      nodeJet2N02705MinusPointP024Radius2577]

theorem nodeJet2N02705MinusPointP024DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP024Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP024RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP024Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP024Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP024Rounded2577]

def nodeJet2N02705MinusPointP025Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP025Radius2577 : ℝ := ((2199025709631 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705MinusPointP025RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP025Factor2577
        nodeJet2N02705MinusPointP025Center2577) =
        nodeJet2N02705MinusPointP025Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP025RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP025Rounded2577‖ ≤
          nodeJet2N02705MinusPointP025Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP025Factor2577
      nodeJet2N02705MinusPointP025Center2577)
  rw [nodeJet2N02705MinusPointP025RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP025Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP025Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP025Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP025DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP025Factor2577,
      nodeJet2N02705MinusPointP025Error2577, rounding2542,
      nodeJet2N02705MinusPointP025Radius2577]

theorem nodeJet2N02705MinusPointP025DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP025Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP025RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP025Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP025Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP025Rounded2577]

def nodeJet2N02705MinusPointP026Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP026Radius2577 : ℝ := ((1099512854821 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705MinusPointP026RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP026Factor2577
        nodeJet2N02705MinusPointP026Center2577) =
        nodeJet2N02705MinusPointP026Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP026RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP026Rounded2577‖ ≤
          nodeJet2N02705MinusPointP026Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP026Factor2577
      nodeJet2N02705MinusPointP026Center2577)
  rw [nodeJet2N02705MinusPointP026RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP026Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP026Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP026Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP026DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP026Factor2577,
      nodeJet2N02705MinusPointP026Error2577, rounding2542,
      nodeJet2N02705MinusPointP026Radius2577]

theorem nodeJet2N02705MinusPointP026DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP026Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP026RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP026Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP026Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP026Rounded2577]

def nodeJet2N02705MinusPointP027Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP027Radius2577 : ℝ := ((1099512854829 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705MinusPointP027RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP027Factor2577
        nodeJet2N02705MinusPointP027Center2577) =
        nodeJet2N02705MinusPointP027Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP027RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP027Rounded2577‖ ≤
          nodeJet2N02705MinusPointP027Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP027Factor2577
      nodeJet2N02705MinusPointP027Center2577)
  rw [nodeJet2N02705MinusPointP027RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP027Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP027Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP027Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP027DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP027Factor2577,
      nodeJet2N02705MinusPointP027Error2577, rounding2542,
      nodeJet2N02705MinusPointP027Radius2577]

theorem nodeJet2N02705MinusPointP027DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP027Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP027RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP027Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP027Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP027Rounded2577]

def nodeJet2N02705MinusPointP028Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP028Radius2577 : ℝ := ((68719553427 : ℝ) /
        (4 * 10^40
        + 3556142965880123323311949751266331066368))

theorem nodeJet2N02705MinusPointP028RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP028Factor2577
        nodeJet2N02705MinusPointP028Center2577) =
        nodeJet2N02705MinusPointP028Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP028RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP028Rounded2577‖ ≤
          nodeJet2N02705MinusPointP028Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP028Factor2577
      nodeJet2N02705MinusPointP028Center2577)
  rw [nodeJet2N02705MinusPointP028RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP028Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP028Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP028Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP028DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP028Factor2577,
      nodeJet2N02705MinusPointP028Error2577, rounding2542,
      nodeJet2N02705MinusPointP028Radius2577]

theorem nodeJet2N02705MinusPointP028DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP028Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP028RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP028Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP028Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP028Rounded2577]

def nodeJet2N02705MinusPointP029Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP029Radius2577 : ℝ := ((2199025709673 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705MinusPointP029RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705MinusPointP029Factor2577
        nodeJet2N02705MinusPointP029Center2577) =
        nodeJet2N02705MinusPointP029Rounded2577 := by
  cbv

theorem nodeJet2N02705MinusPointP029RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP029Rounded2577‖ ≤
          nodeJet2N02705MinusPointP029Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705MinusPointP029Factor2577
      nodeJet2N02705MinusPointP029Center2577)
  rw [nodeJet2N02705MinusPointP029RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP029Factor2577 * embedPair2542
        nodeJet2N02705MinusPointP029Center2577)
    (embedPair2542 nodeJet2N02705MinusPointP029Rounded2577)).trans (add_le_add
        nodeJet2N02705MinusPointP029DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705MinusPointP029Factor2577,
      nodeJet2N02705MinusPointP029Error2577, rounding2542,
      nodeJet2N02705MinusPointP029Radius2577]

theorem nodeJet2N02705MinusPointP029DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02705MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02705MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02705MinusPointPosition2577)
    (embedPair2542 nodeJet2N02705MinusPointP029Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705MinusPointP029RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705MinusPointP029Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705MinusPointP029Radius2577, pairMagnitude2542,
      nodeJet2N02705MinusPointP029Rounded2577]

noncomputable def nodeJet2N02705MinusSignedValue2577 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 nodeJet2N02705MinusPointP000Rounded2577
  | 1 => embedPair2542 nodeJet2N02705MinusPointP001Rounded2577
  | 2 => embedPair2542 nodeJet2N02705MinusPointP002Rounded2577
  | 3 => embedPair2542 nodeJet2N02705MinusPointP003Rounded2577
  | 4 => embedPair2542 nodeJet2N02705MinusPointP004Rounded2577
  | 5 => embedPair2542 nodeJet2N02705MinusPointP005Rounded2577
  | 6 => embedPair2542 nodeJet2N02705MinusPointP006Rounded2577
  | 7 => embedPair2542 nodeJet2N02705MinusPointP007Rounded2577
  | 8 => embedPair2542 nodeJet2N02705MinusPointP008Rounded2577
  | 9 => embedPair2542 nodeJet2N02705MinusPointP009Rounded2577
  | 10 => embedPair2542 nodeJet2N02705MinusPointP010Rounded2577
  | 11 => embedPair2542 nodeJet2N02705MinusPointP011Rounded2577
  | 12 => embedPair2542 nodeJet2N02705MinusPointP012Rounded2577
  | 13 => embedPair2542 nodeJet2N02705MinusPointP013Rounded2577
  | 14 => embedPair2542 nodeJet2N02705MinusPointP014Rounded2577
  | 15 => embedPair2542 nodeJet2N02705MinusPointP015Rounded2577
  | 16 => embedPair2542 nodeJet2N02705MinusPointP016Rounded2577
  | 17 => embedPair2542 nodeJet2N02705MinusPointP017Rounded2577
  | 18 => embedPair2542 nodeJet2N02705MinusPointP018Rounded2577
  | 19 => embedPair2542 nodeJet2N02705MinusPointP019Rounded2577
  | 20 => embedPair2542 nodeJet2N02705MinusPointP020Rounded2577
  | 21 => embedPair2542 nodeJet2N02705MinusPointP021Rounded2577
  | 22 => embedPair2542 nodeJet2N02705MinusPointP022Rounded2577
  | 23 => embedPair2542 nodeJet2N02705MinusPointP023Rounded2577
  | 24 => embedPair2542 nodeJet2N02705MinusPointP024Rounded2577
  | 25 => embedPair2542 nodeJet2N02705MinusPointP025Rounded2577
  | 26 => embedPair2542 nodeJet2N02705MinusPointP026Rounded2577
  | 27 => embedPair2542 nodeJet2N02705MinusPointP027Rounded2577
  | 28 => embedPair2542 nodeJet2N02705MinusPointP028Rounded2577
  | 29 => embedPair2542 nodeJet2N02705MinusPointP029Rounded2577
  | _ => 0

noncomputable def nodeJet2N02705MinusSignedError2577 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => nodeJet2N02705MinusPointP000Radius2577
  | 1 => nodeJet2N02705MinusPointP001Radius2577
  | 2 => nodeJet2N02705MinusPointP002Radius2577
  | 3 => nodeJet2N02705MinusPointP003Radius2577
  | 4 => nodeJet2N02705MinusPointP004Radius2577
  | 5 => nodeJet2N02705MinusPointP005Radius2577
  | 6 => nodeJet2N02705MinusPointP006Radius2577
  | 7 => nodeJet2N02705MinusPointP007Radius2577
  | 8 => nodeJet2N02705MinusPointP008Radius2577
  | 9 => nodeJet2N02705MinusPointP009Radius2577
  | 10 => nodeJet2N02705MinusPointP010Radius2577
  | 11 => nodeJet2N02705MinusPointP011Radius2577
  | 12 => nodeJet2N02705MinusPointP012Radius2577
  | 13 => nodeJet2N02705MinusPointP013Radius2577
  | 14 => nodeJet2N02705MinusPointP014Radius2577
  | 15 => nodeJet2N02705MinusPointP015Radius2577
  | 16 => nodeJet2N02705MinusPointP016Radius2577
  | 17 => nodeJet2N02705MinusPointP017Radius2577
  | 18 => nodeJet2N02705MinusPointP018Radius2577
  | 19 => nodeJet2N02705MinusPointP019Radius2577
  | 20 => nodeJet2N02705MinusPointP020Radius2577
  | 21 => nodeJet2N02705MinusPointP021Radius2577
  | 22 => nodeJet2N02705MinusPointP022Radius2577
  | 23 => nodeJet2N02705MinusPointP023Radius2577
  | 24 => nodeJet2N02705MinusPointP024Radius2577
  | 25 => nodeJet2N02705MinusPointP025Radius2577
  | 26 => nodeJet2N02705MinusPointP026Radius2577
  | 27 => nodeJet2N02705MinusPointP027Radius2577
  | 28 => nodeJet2N02705MinusPointP028Radius2577
  | 29 => nodeJet2N02705MinusPointP029Radius2577
  | _ => 0

theorem nodeJet2N02705MinusSignedExpError2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02705MinusPointPosition2577 -
        nodeJet2N02705MinusSignedValue2577 i‖ ≤ nodeJet2N02705MinusSignedError2577 i := by
  fin_cases i
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP000RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP001RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP002RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP003RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP004RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP005RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP006RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP007RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP008RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP009RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP010RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP011RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP012RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP013RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP014RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP015RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP016RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP017RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP018RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP019RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP020RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP021RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP022RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP023RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP024RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP025RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP026RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP027RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP028RoundedError2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP029RoundedError2577

theorem nodeJet2N02705MinusSignedUnitNorm2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02705MinusPointPosition2577‖ ≤ 1
        := by
  fin_cases i
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP000DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP001DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP002DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP003DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP004DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP005DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP006DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP007DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP008DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP009DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP010DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP011DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP012DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP013DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP014DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP015DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP016DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP017DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP018DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP019DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP020DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP021DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP022DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP023DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP024DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP025DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP026DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP027DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP028DerivativeNorm2577
  · simpa only [nodeJet2N02705MinusSignedValue2577, nodeJet2N02705MinusSignedError2577] using
      nodeJet2N02705MinusPointP029DerivativeNorm2577

noncomputable def nodeJet2N02705MinusSignedSum2577 : ℂ := ⟨(((-(((30244723229424 * 10^40
        + 8843211144416928748504654638697754799563) * 10^40
        + 3501093671214480362153867529409315354009) * 10^40
        + 4937741437054316836707234037847086035085)) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888)),
    (((((19684510182963 * 10^40
        + 6049648659512024512357756926752073009330) * 10^40
        + 9216517925178363852591791753804539771220) * 10^40
        + 2496491253650107164437560716486869474517) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888))⟩

noncomputable def nodeJet2N02705MinusSignedUpper2577 : ℝ := ((2541994599 : ℝ) /
        100000000)

theorem nodeJet2N02705MinusSignedSum_eq2577 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02705MinusSignedValue2577 i) =
      nodeJet2N02705MinusSignedSum2577 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        nodeJet2N02705MinusSignedValue2577,
      nodeJet2N02705MinusSignedSum2577, embedPair2542, nodeJet2N02705MinusPointP000Rounded2577,
      nodeJet2N02705MinusPointP001Rounded2577,
      nodeJet2N02705MinusPointP002Rounded2577,
      nodeJet2N02705MinusPointP003Rounded2577,
      nodeJet2N02705MinusPointP004Rounded2577,
      nodeJet2N02705MinusPointP005Rounded2577,
      nodeJet2N02705MinusPointP006Rounded2577,
      nodeJet2N02705MinusPointP007Rounded2577,
      nodeJet2N02705MinusPointP008Rounded2577,
      nodeJet2N02705MinusPointP009Rounded2577,
      nodeJet2N02705MinusPointP010Rounded2577,
      nodeJet2N02705MinusPointP011Rounded2577,
      nodeJet2N02705MinusPointP012Rounded2577,
      nodeJet2N02705MinusPointP013Rounded2577,
      nodeJet2N02705MinusPointP014Rounded2577,
      nodeJet2N02705MinusPointP015Rounded2577,
      nodeJet2N02705MinusPointP016Rounded2577,
      nodeJet2N02705MinusPointP017Rounded2577,
      nodeJet2N02705MinusPointP018Rounded2577,
      nodeJet2N02705MinusPointP019Rounded2577,
      nodeJet2N02705MinusPointP020Rounded2577,
      nodeJet2N02705MinusPointP021Rounded2577,
      nodeJet2N02705MinusPointP022Rounded2577,
      nodeJet2N02705MinusPointP023Rounded2577,
      nodeJet2N02705MinusPointP024Rounded2577,
      nodeJet2N02705MinusPointP025Rounded2577,
      nodeJet2N02705MinusPointP026Rounded2577,
      nodeJet2N02705MinusPointP027Rounded2577,
      nodeJet2N02705MinusPointP028Rounded2577,
      nodeJet2N02705MinusPointP029Rounded2577, Complex.mul_re, Complex.mul_im]

theorem nodeJet2N02705MinusSignedSum_norm2577 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02705MinusSignedValue2577 i‖ ≤
        ((2541994589 :
        ℝ) /
        100000000) := by
  rw [nodeJet2N02705MinusSignedSum_eq2577]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [nodeJet2N02705MinusSignedSum2577]

theorem nodeJet2N02705MinusSignedCharge2577 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02705MinusSignedError2577 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      nodeJet2N02705MinusSignedError2577, nodeJet2N02705MinusPointP000Radius2577,
      nodeJet2N02705MinusPointP001Radius2577,
      nodeJet2N02705MinusPointP002Radius2577,
      nodeJet2N02705MinusPointP003Radius2577,
      nodeJet2N02705MinusPointP004Radius2577,
      nodeJet2N02705MinusPointP005Radius2577,
      nodeJet2N02705MinusPointP006Radius2577,
      nodeJet2N02705MinusPointP007Radius2577,
      nodeJet2N02705MinusPointP008Radius2577,
      nodeJet2N02705MinusPointP009Radius2577,
      nodeJet2N02705MinusPointP010Radius2577,
      nodeJet2N02705MinusPointP011Radius2577,
      nodeJet2N02705MinusPointP012Radius2577,
      nodeJet2N02705MinusPointP013Radius2577,
      nodeJet2N02705MinusPointP014Radius2577,
      nodeJet2N02705MinusPointP015Radius2577,
      nodeJet2N02705MinusPointP016Radius2577,
      nodeJet2N02705MinusPointP017Radius2577,
      nodeJet2N02705MinusPointP018Radius2577,
      nodeJet2N02705MinusPointP019Radius2577,
      nodeJet2N02705MinusPointP020Radius2577,
      nodeJet2N02705MinusPointP021Radius2577,
      nodeJet2N02705MinusPointP022Radius2577,
      nodeJet2N02705MinusPointP023Radius2577,
      nodeJet2N02705MinusPointP024Radius2577,
      nodeJet2N02705MinusPointP025Radius2577,
      nodeJet2N02705MinusPointP026Radius2577,
      nodeJet2N02705MinusPointP027Radius2577,
      nodeJet2N02705MinusPointP028Radius2577,
      nodeJet2N02705MinusPointP029Radius2577]

theorem nodeJet2N02705MinusSignedUpper_le2577 :
    signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 nodeJet2N02705MinusPointPosition2577 ≤ nodeJet2N02705MinusSignedUpper2577
          := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02705MinusPointPosition2577‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02705MinusSignedValue2577 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02705MinusSignedError2577 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (nodeJet2N02705MinusSignedExpError2577
        i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02705MinusPointPosition2577‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (nodeJet2N02705MinusSignedUnitNorm2577 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02705MinusPointPosition2577‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 nodeJet2N02705MinusSignedUpper2577
  linarith [nodeJet2N02705MinusSignedSum_norm2577, nodeJet2N02705MinusSignedCharge2577]

theorem nodeJet2N02705MinusPhysical2577 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        nodeJet2N02705MinusPointPosition2577‖ ≤
      nodeJet2N02705MinusSignedUpper2577 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        nodeJet2N02705MinusPointPosition2577
  exact h.trans nodeJet2N02705MinusSignedUpper_le2577

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.nodeJet2N02705MinusSignedExpError2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02705MinusSignedSum_eq2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02705MinusSignedCharge2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02705MinusSignedUpper_le2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02705MinusPhysical2577
