import ConnesWeilRH.Dev.C1RouteANodeJet2N02703Minus2577
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem nodeJet2N02703MinusPoint_triangle2577 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def nodeJet2N02703MinusPointP000Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP000Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02703MinusPointP000RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP000Factor2577
        nodeJet2N02703MinusPointP000Center2577) =
        nodeJet2N02703MinusPointP000Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP000RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP000Rounded2577‖ ≤
          nodeJet2N02703MinusPointP000Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP000Factor2577
      nodeJet2N02703MinusPointP000Center2577)
  rw [nodeJet2N02703MinusPointP000RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP000Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP000Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP000Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP000DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP000Factor2577,
      nodeJet2N02703MinusPointP000Error2577, rounding2542,
      nodeJet2N02703MinusPointP000Radius2577]

theorem nodeJet2N02703MinusPointP000DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP000Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP000RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP000Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP000Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP000Rounded2577]

def nodeJet2N02703MinusPointP001Rounded2577 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP001Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP001RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP001Factor2577
        nodeJet2N02703MinusPointP001Center2577) =
        nodeJet2N02703MinusPointP001Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP001RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP001Rounded2577‖ ≤
          nodeJet2N02703MinusPointP001Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP001Factor2577
      nodeJet2N02703MinusPointP001Center2577)
  rw [nodeJet2N02703MinusPointP001RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP001Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP001Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP001Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP001DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP001Factor2577,
      nodeJet2N02703MinusPointP001Error2577, rounding2542,
      nodeJet2N02703MinusPointP001Radius2577]

theorem nodeJet2N02703MinusPointP001DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP001Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP001RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP001Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP001Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP001Rounded2577]

def nodeJet2N02703MinusPointP002Rounded2577 : RatPair2542 :=
  (((9098397 : ℚ) /
        316912650057057350374175801344),
    (((-1269627) : ℚ) /
        79228162514264337593543950336))

noncomputable def nodeJet2N02703MinusPointP002Radius2577 : ℝ := ((1099511707161 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02703MinusPointP002RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP002Factor2577
        nodeJet2N02703MinusPointP002Center2577) =
        nodeJet2N02703MinusPointP002Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP002RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP002Rounded2577‖ ≤
          nodeJet2N02703MinusPointP002Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP002Factor2577
      nodeJet2N02703MinusPointP002Center2577)
  rw [nodeJet2N02703MinusPointP002RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP002Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP002Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP002Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP002DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP002Factor2577,
      nodeJet2N02703MinusPointP002Error2577, rounding2542,
      nodeJet2N02703MinusPointP002Radius2577]

theorem nodeJet2N02703MinusPointP002DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP002Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP002RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP002Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP002Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP002Rounded2577]

def nodeJet2N02703MinusPointP003Rounded2577 : RatPair2542 :=
  (((331334872451921 : ℚ) /
        1267650600228229401496703205376),
    ((9091509374249 : ℚ) /
        79228162514264337593543950336))

noncomputable def nodeJet2N02703MinusPointP003Radius2577 : ℝ := ((993542856051 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02703MinusPointP003RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP003Factor2577
        nodeJet2N02703MinusPointP003Center2577) =
        nodeJet2N02703MinusPointP003Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP003RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP003Rounded2577‖ ≤
          nodeJet2N02703MinusPointP003Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP003Factor2577
      nodeJet2N02703MinusPointP003Center2577)
  rw [nodeJet2N02703MinusPointP003RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP003Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP003Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP003Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP003DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP003Factor2577,
      nodeJet2N02703MinusPointP003Error2577, rounding2542,
      nodeJet2N02703MinusPointP003Radius2577]

theorem nodeJet2N02703MinusPointP003DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP003Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP003RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP003Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP003Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP003Rounded2577]

def nodeJet2N02703MinusPointP004Rounded2577 : RatPair2542 :=
  (((119053098351406123 : ℚ) /
        1267650600228229401496703205376),
    (((-110808274023828901) : ℚ) /
        1267650600228229401496703205376))

noncomputable def nodeJet2N02703MinusPointP004Radius2577 : ℝ := ((353951922743703 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02703MinusPointP004RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP004Factor2577
        nodeJet2N02703MinusPointP004Center2577) =
        nodeJet2N02703MinusPointP004Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP004RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP004Rounded2577‖ ≤
          nodeJet2N02703MinusPointP004Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP004Factor2577
      nodeJet2N02703MinusPointP004Center2577)
  rw [nodeJet2N02703MinusPointP004RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP004Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP004Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP004Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP004DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP004Factor2577,
      nodeJet2N02703MinusPointP004Error2577, rounding2542,
      nodeJet2N02703MinusPointP004Radius2577]

theorem nodeJet2N02703MinusPointP004DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP004Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP004RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP004Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP004Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP004Rounded2577]

def nodeJet2N02703MinusPointP005Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP005Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02703MinusPointP005RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP005Factor2577
        nodeJet2N02703MinusPointP005Center2577) =
        nodeJet2N02703MinusPointP005Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP005RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP005Rounded2577‖ ≤
          nodeJet2N02703MinusPointP005Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP005Factor2577
      nodeJet2N02703MinusPointP005Center2577)
  rw [nodeJet2N02703MinusPointP005RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP005Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP005Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP005Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP005DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP005Factor2577,
      nodeJet2N02703MinusPointP005Error2577, rounding2542,
      nodeJet2N02703MinusPointP005Radius2577]

theorem nodeJet2N02703MinusPointP005DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP005Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP005RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP005Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP005Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP005Rounded2577]

def nodeJet2N02703MinusPointP006Rounded2577 : RatPair2542 :=
  (((109 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP006Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP006RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP006Factor2577
        nodeJet2N02703MinusPointP006Center2577) =
        nodeJet2N02703MinusPointP006Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP006RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP006Rounded2577‖ ≤
          nodeJet2N02703MinusPointP006Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP006Factor2577
      nodeJet2N02703MinusPointP006Center2577)
  rw [nodeJet2N02703MinusPointP006RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP006Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP006Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP006Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP006DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP006Factor2577,
      nodeJet2N02703MinusPointP006Error2577, rounding2542,
      nodeJet2N02703MinusPointP006Radius2577]

theorem nodeJet2N02703MinusPointP006DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP006Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP006RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP006Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP006Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP006Rounded2577]

def nodeJet2N02703MinusPointP007Rounded2577 : RatPair2542 :=
  (((18328487642933 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP007Radius2577 : ℝ := ((1102046923717 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02703MinusPointP007RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP007Factor2577
        nodeJet2N02703MinusPointP007Center2577) =
        nodeJet2N02703MinusPointP007Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP007RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP007Rounded2577‖ ≤
          nodeJet2N02703MinusPointP007Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP007Factor2577
      nodeJet2N02703MinusPointP007Center2577)
  rw [nodeJet2N02703MinusPointP007RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP007Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP007Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP007Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP007DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP007Factor2577,
      nodeJet2N02703MinusPointP007Error2577, rounding2542,
      nodeJet2N02703MinusPointP007Radius2577]

theorem nodeJet2N02703MinusPointP007DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP007Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP007RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP007Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP007Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP007Rounded2577]

def nodeJet2N02703MinusPointP008Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP008Radius2577 : ℝ := ((2199042191689 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP008RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP008Factor2577
        nodeJet2N02703MinusPointP008Center2577) =
        nodeJet2N02703MinusPointP008Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP008RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP008Rounded2577‖ ≤
          nodeJet2N02703MinusPointP008Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP008Factor2577
      nodeJet2N02703MinusPointP008Center2577)
  rw [nodeJet2N02703MinusPointP008RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP008Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP008Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP008Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP008DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP008Factor2577,
      nodeJet2N02703MinusPointP008Error2577, rounding2542,
      nodeJet2N02703MinusPointP008Radius2577]

theorem nodeJet2N02703MinusPointP008DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP008Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP008RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP008Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP008Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP008Rounded2577]

def nodeJet2N02703MinusPointP009Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP009Radius2577 : ℝ := ((2199042191771 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP009RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP009Factor2577
        nodeJet2N02703MinusPointP009Center2577) =
        nodeJet2N02703MinusPointP009Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP009RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP009Rounded2577‖ ≤
          nodeJet2N02703MinusPointP009Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP009Factor2577
      nodeJet2N02703MinusPointP009Center2577)
  rw [nodeJet2N02703MinusPointP009RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP009Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP009Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP009Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP009DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP009Factor2577,
      nodeJet2N02703MinusPointP009Error2577, rounding2542,
      nodeJet2N02703MinusPointP009Radius2577]

theorem nodeJet2N02703MinusPointP009DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP009Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP009RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP009Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP009Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP009Rounded2577]

def nodeJet2N02703MinusPointP010Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP010Radius2577 : ℝ := ((2199042191819 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP010RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP010Factor2577
        nodeJet2N02703MinusPointP010Center2577) =
        nodeJet2N02703MinusPointP010Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP010RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP010Rounded2577‖ ≤
          nodeJet2N02703MinusPointP010Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP010Factor2577
      nodeJet2N02703MinusPointP010Center2577)
  rw [nodeJet2N02703MinusPointP010RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP010Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP010Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP010Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP010DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP010Factor2577,
      nodeJet2N02703MinusPointP010Error2577, rounding2542,
      nodeJet2N02703MinusPointP010Radius2577]

theorem nodeJet2N02703MinusPointP010DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP010Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP010RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP010Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP010Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP010Rounded2577]

def nodeJet2N02703MinusPointP011Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP011Radius2577 : ℝ := ((2199042191851 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP011RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP011Factor2577
        nodeJet2N02703MinusPointP011Center2577) =
        nodeJet2N02703MinusPointP011Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP011RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP011Rounded2577‖ ≤
          nodeJet2N02703MinusPointP011Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP011Factor2577
      nodeJet2N02703MinusPointP011Center2577)
  rw [nodeJet2N02703MinusPointP011RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP011Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP011Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP011Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP011DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP011Factor2577,
      nodeJet2N02703MinusPointP011Error2577, rounding2542,
      nodeJet2N02703MinusPointP011Radius2577]

theorem nodeJet2N02703MinusPointP011DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP011Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP011RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP011Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP011Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP011Rounded2577]

def nodeJet2N02703MinusPointP012Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP012Radius2577 : ℝ := ((549760547971 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02703MinusPointP012RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP012Factor2577
        nodeJet2N02703MinusPointP012Center2577) =
        nodeJet2N02703MinusPointP012Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP012RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP012Rounded2577‖ ≤
          nodeJet2N02703MinusPointP012Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP012Factor2577
      nodeJet2N02703MinusPointP012Center2577)
  rw [nodeJet2N02703MinusPointP012RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP012Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP012Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP012Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP012DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP012Factor2577,
      nodeJet2N02703MinusPointP012Error2577, rounding2542,
      nodeJet2N02703MinusPointP012Radius2577]

theorem nodeJet2N02703MinusPointP012DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP012Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP012RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP012Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP012Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP012Rounded2577]

def nodeJet2N02703MinusPointP013Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP013Radius2577 : ℝ := ((2199042191915 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP013RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP013Factor2577
        nodeJet2N02703MinusPointP013Center2577) =
        nodeJet2N02703MinusPointP013Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP013RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP013Rounded2577‖ ≤
          nodeJet2N02703MinusPointP013Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP013Factor2577
      nodeJet2N02703MinusPointP013Center2577)
  rw [nodeJet2N02703MinusPointP013RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP013Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP013Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP013Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP013DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP013Factor2577,
      nodeJet2N02703MinusPointP013Error2577, rounding2542,
      nodeJet2N02703MinusPointP013Radius2577]

theorem nodeJet2N02703MinusPointP013DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP013Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP013RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP013Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP013Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP013Rounded2577]

def nodeJet2N02703MinusPointP014Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP014Radius2577 : ℝ := ((1099521095985 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02703MinusPointP014RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP014Factor2577
        nodeJet2N02703MinusPointP014Center2577) =
        nodeJet2N02703MinusPointP014Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP014RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP014Rounded2577‖ ≤
          nodeJet2N02703MinusPointP014Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP014Factor2577
      nodeJet2N02703MinusPointP014Center2577)
  rw [nodeJet2N02703MinusPointP014RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP014Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP014Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP014Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP014DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP014Factor2577,
      nodeJet2N02703MinusPointP014Error2577, rounding2542,
      nodeJet2N02703MinusPointP014Radius2577]

theorem nodeJet2N02703MinusPointP014DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP014Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP014RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP014Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP014Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP014Rounded2577]

def nodeJet2N02703MinusPointP015Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP015Radius2577 : ℝ := ((2199042192011 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP015RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP015Factor2577
        nodeJet2N02703MinusPointP015Center2577) =
        nodeJet2N02703MinusPointP015Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP015RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP015Rounded2577‖ ≤
          nodeJet2N02703MinusPointP015Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP015Factor2577
      nodeJet2N02703MinusPointP015Center2577)
  rw [nodeJet2N02703MinusPointP015RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP015Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP015Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP015Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP015DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP015Factor2577,
      nodeJet2N02703MinusPointP015Error2577, rounding2542,
      nodeJet2N02703MinusPointP015Radius2577]

theorem nodeJet2N02703MinusPointP015DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP015Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP015RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP015Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP015Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP015Rounded2577]

def nodeJet2N02703MinusPointP016Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP016Radius2577 : ℝ := ((2199042192039 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP016RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP016Factor2577
        nodeJet2N02703MinusPointP016Center2577) =
        nodeJet2N02703MinusPointP016Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP016RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP016Rounded2577‖ ≤
          nodeJet2N02703MinusPointP016Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP016Factor2577
      nodeJet2N02703MinusPointP016Center2577)
  rw [nodeJet2N02703MinusPointP016RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP016Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP016Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP016Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP016DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP016Factor2577,
      nodeJet2N02703MinusPointP016Error2577, rounding2542,
      nodeJet2N02703MinusPointP016Radius2577]

theorem nodeJet2N02703MinusPointP016DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP016Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP016RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP016Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP016Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP016Rounded2577]

def nodeJet2N02703MinusPointP017Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP017Radius2577 : ℝ := ((68720068503 : ℝ) /
        (4 * 10^40
        + 3556142965880123323311949751266331066368))

theorem nodeJet2N02703MinusPointP017RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP017Factor2577
        nodeJet2N02703MinusPointP017Center2577) =
        nodeJet2N02703MinusPointP017Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP017RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP017Rounded2577‖ ≤
          nodeJet2N02703MinusPointP017Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP017Factor2577
      nodeJet2N02703MinusPointP017Center2577)
  rw [nodeJet2N02703MinusPointP017RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP017Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP017Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP017Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP017DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP017Factor2577,
      nodeJet2N02703MinusPointP017Error2577, rounding2542,
      nodeJet2N02703MinusPointP017Radius2577]

theorem nodeJet2N02703MinusPointP017DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP017Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP017RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP017Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP017Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP017Rounded2577]

def nodeJet2N02703MinusPointP018Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP018Radius2577 : ℝ := ((2199042192117 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP018RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP018Factor2577
        nodeJet2N02703MinusPointP018Center2577) =
        nodeJet2N02703MinusPointP018Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP018RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP018Rounded2577‖ ≤
          nodeJet2N02703MinusPointP018Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP018Factor2577
      nodeJet2N02703MinusPointP018Center2577)
  rw [nodeJet2N02703MinusPointP018RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP018Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP018Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP018Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP018DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP018Factor2577,
      nodeJet2N02703MinusPointP018Error2577, rounding2542,
      nodeJet2N02703MinusPointP018Radius2577]

theorem nodeJet2N02703MinusPointP018DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP018Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP018RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP018Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP018Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP018Rounded2577]

def nodeJet2N02703MinusPointP019Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP019Radius2577 : ℝ := ((2199042192155 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP019RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP019Factor2577
        nodeJet2N02703MinusPointP019Center2577) =
        nodeJet2N02703MinusPointP019Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP019RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP019Rounded2577‖ ≤
          nodeJet2N02703MinusPointP019Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP019Factor2577
      nodeJet2N02703MinusPointP019Center2577)
  rw [nodeJet2N02703MinusPointP019RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP019Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP019Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP019Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP019DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP019Factor2577,
      nodeJet2N02703MinusPointP019Error2577, rounding2542,
      nodeJet2N02703MinusPointP019Radius2577]

theorem nodeJet2N02703MinusPointP019DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP019Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP019RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP019Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP019Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP019Rounded2577]

def nodeJet2N02703MinusPointP020Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP020Radius2577 : ℝ := ((2199042192197 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP020RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP020Factor2577
        nodeJet2N02703MinusPointP020Center2577) =
        nodeJet2N02703MinusPointP020Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP020RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP020Rounded2577‖ ≤
          nodeJet2N02703MinusPointP020Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP020Factor2577
      nodeJet2N02703MinusPointP020Center2577)
  rw [nodeJet2N02703MinusPointP020RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP020Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP020Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP020Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP020DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP020Factor2577,
      nodeJet2N02703MinusPointP020Error2577, rounding2542,
      nodeJet2N02703MinusPointP020Radius2577]

theorem nodeJet2N02703MinusPointP020DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP020Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP020RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP020Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP020Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP020Rounded2577]

def nodeJet2N02703MinusPointP021Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP021Radius2577 : ℝ := ((274880274029 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem nodeJet2N02703MinusPointP021RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP021Factor2577
        nodeJet2N02703MinusPointP021Center2577) =
        nodeJet2N02703MinusPointP021Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP021RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP021Rounded2577‖ ≤
          nodeJet2N02703MinusPointP021Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP021Factor2577
      nodeJet2N02703MinusPointP021Center2577)
  rw [nodeJet2N02703MinusPointP021RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP021Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP021Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP021Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP021DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP021Factor2577,
      nodeJet2N02703MinusPointP021Error2577, rounding2542,
      nodeJet2N02703MinusPointP021Radius2577]

theorem nodeJet2N02703MinusPointP021DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP021Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP021RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP021Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP021Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP021Rounded2577]

def nodeJet2N02703MinusPointP022Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP022Radius2577 : ℝ := ((1099521096125 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02703MinusPointP022RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP022Factor2577
        nodeJet2N02703MinusPointP022Center2577) =
        nodeJet2N02703MinusPointP022Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP022RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP022Rounded2577‖ ≤
          nodeJet2N02703MinusPointP022Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP022Factor2577
      nodeJet2N02703MinusPointP022Center2577)
  rw [nodeJet2N02703MinusPointP022RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP022Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP022Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP022Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP022DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP022Factor2577,
      nodeJet2N02703MinusPointP022Error2577, rounding2542,
      nodeJet2N02703MinusPointP022Radius2577]

theorem nodeJet2N02703MinusPointP022DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP022Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP022RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP022Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP022Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP022Rounded2577]

def nodeJet2N02703MinusPointP023Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP023Radius2577 : ℝ := ((2199042192301 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP023RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP023Factor2577
        nodeJet2N02703MinusPointP023Center2577) =
        nodeJet2N02703MinusPointP023Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP023RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP023Rounded2577‖ ≤
          nodeJet2N02703MinusPointP023Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP023Factor2577
      nodeJet2N02703MinusPointP023Center2577)
  rw [nodeJet2N02703MinusPointP023RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP023Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP023Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP023Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP023DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP023Factor2577,
      nodeJet2N02703MinusPointP023Error2577, rounding2542,
      nodeJet2N02703MinusPointP023Radius2577]

theorem nodeJet2N02703MinusPointP023DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP023Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP023RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP023Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP023Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP023Rounded2577]

def nodeJet2N02703MinusPointP024Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP024Radius2577 : ℝ := ((2199042192325 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP024RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP024Factor2577
        nodeJet2N02703MinusPointP024Center2577) =
        nodeJet2N02703MinusPointP024Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP024RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP024Rounded2577‖ ≤
          nodeJet2N02703MinusPointP024Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP024Factor2577
      nodeJet2N02703MinusPointP024Center2577)
  rw [nodeJet2N02703MinusPointP024RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP024Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP024Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP024Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP024DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP024Factor2577,
      nodeJet2N02703MinusPointP024Error2577, rounding2542,
      nodeJet2N02703MinusPointP024Radius2577]

theorem nodeJet2N02703MinusPointP024DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP024Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP024RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP024Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP024Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP024Rounded2577]

def nodeJet2N02703MinusPointP025Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP025Radius2577 : ℝ := ((2199042192355 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP025RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP025Factor2577
        nodeJet2N02703MinusPointP025Center2577) =
        nodeJet2N02703MinusPointP025Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP025RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP025Rounded2577‖ ≤
          nodeJet2N02703MinusPointP025Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP025Factor2577
      nodeJet2N02703MinusPointP025Center2577)
  rw [nodeJet2N02703MinusPointP025RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP025Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP025Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP025Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP025DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP025Factor2577,
      nodeJet2N02703MinusPointP025Error2577, rounding2542,
      nodeJet2N02703MinusPointP025Radius2577]

theorem nodeJet2N02703MinusPointP025DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP025Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP025RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP025Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP025Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP025Rounded2577]

def nodeJet2N02703MinusPointP026Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP026Radius2577 : ℝ := ((2199042192385 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP026RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP026Factor2577
        nodeJet2N02703MinusPointP026Center2577) =
        nodeJet2N02703MinusPointP026Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP026RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP026Rounded2577‖ ≤
          nodeJet2N02703MinusPointP026Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP026Factor2577
      nodeJet2N02703MinusPointP026Center2577)
  rw [nodeJet2N02703MinusPointP026RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP026Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP026Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP026Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP026DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP026Factor2577,
      nodeJet2N02703MinusPointP026Error2577, rounding2542,
      nodeJet2N02703MinusPointP026Radius2577]

theorem nodeJet2N02703MinusPointP026DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP026Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP026RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP026Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP026Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP026Rounded2577]

def nodeJet2N02703MinusPointP027Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP027Radius2577 : ℝ := ((2199042192429 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703MinusPointP027RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP027Factor2577
        nodeJet2N02703MinusPointP027Center2577) =
        nodeJet2N02703MinusPointP027Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP027RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP027Rounded2577‖ ≤
          nodeJet2N02703MinusPointP027Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP027Factor2577
      nodeJet2N02703MinusPointP027Center2577)
  rw [nodeJet2N02703MinusPointP027RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP027Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP027Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP027Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP027DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP027Factor2577,
      nodeJet2N02703MinusPointP027Error2577, rounding2542,
      nodeJet2N02703MinusPointP027Radius2577]

theorem nodeJet2N02703MinusPointP027DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP027Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP027RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP027Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP027Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP027Rounded2577]

def nodeJet2N02703MinusPointP028Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP028Radius2577 : ℝ := ((1099521096223 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02703MinusPointP028RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP028Factor2577
        nodeJet2N02703MinusPointP028Center2577) =
        nodeJet2N02703MinusPointP028Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP028RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP028Rounded2577‖ ≤
          nodeJet2N02703MinusPointP028Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP028Factor2577
      nodeJet2N02703MinusPointP028Center2577)
  rw [nodeJet2N02703MinusPointP028RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP028Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP028Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP028Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP028DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP028Factor2577,
      nodeJet2N02703MinusPointP028Error2577, rounding2542,
      nodeJet2N02703MinusPointP028Radius2577]

theorem nodeJet2N02703MinusPointP028DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP028Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP028RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP028Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP028Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP028Rounded2577]

def nodeJet2N02703MinusPointP029Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703MinusPointP029Radius2577 : ℝ := ((274880274059 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem nodeJet2N02703MinusPointP029RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703MinusPointP029Factor2577
        nodeJet2N02703MinusPointP029Center2577) =
        nodeJet2N02703MinusPointP029Rounded2577 := by
  cbv

theorem nodeJet2N02703MinusPointP029RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02703MinusPointPosition2577 -
      embedPair2542 nodeJet2N02703MinusPointP029Rounded2577‖ ≤
          nodeJet2N02703MinusPointP029Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703MinusPointP029Factor2577
      nodeJet2N02703MinusPointP029Center2577)
  rw [nodeJet2N02703MinusPointP029RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP029Factor2577 * embedPair2542
        nodeJet2N02703MinusPointP029Center2577)
    (embedPair2542 nodeJet2N02703MinusPointP029Rounded2577)).trans (add_le_add
        nodeJet2N02703MinusPointP029DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703MinusPointP029Factor2577,
      nodeJet2N02703MinusPointP029Error2577, rounding2542,
      nodeJet2N02703MinusPointP029Radius2577]

theorem nodeJet2N02703MinusPointP029DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02703MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02703MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02703MinusPointPosition2577)
    (embedPair2542 nodeJet2N02703MinusPointP029Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703MinusPointP029RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703MinusPointP029Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703MinusPointP029Radius2577, pairMagnitude2542,
      nodeJet2N02703MinusPointP029Rounded2577]

noncomputable def nodeJet2N02703MinusSignedValue2577 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 nodeJet2N02703MinusPointP000Rounded2577
  | 1 => embedPair2542 nodeJet2N02703MinusPointP001Rounded2577
  | 2 => embedPair2542 nodeJet2N02703MinusPointP002Rounded2577
  | 3 => embedPair2542 nodeJet2N02703MinusPointP003Rounded2577
  | 4 => embedPair2542 nodeJet2N02703MinusPointP004Rounded2577
  | 5 => embedPair2542 nodeJet2N02703MinusPointP005Rounded2577
  | 6 => embedPair2542 nodeJet2N02703MinusPointP006Rounded2577
  | 7 => embedPair2542 nodeJet2N02703MinusPointP007Rounded2577
  | 8 => embedPair2542 nodeJet2N02703MinusPointP008Rounded2577
  | 9 => embedPair2542 nodeJet2N02703MinusPointP009Rounded2577
  | 10 => embedPair2542 nodeJet2N02703MinusPointP010Rounded2577
  | 11 => embedPair2542 nodeJet2N02703MinusPointP011Rounded2577
  | 12 => embedPair2542 nodeJet2N02703MinusPointP012Rounded2577
  | 13 => embedPair2542 nodeJet2N02703MinusPointP013Rounded2577
  | 14 => embedPair2542 nodeJet2N02703MinusPointP014Rounded2577
  | 15 => embedPair2542 nodeJet2N02703MinusPointP015Rounded2577
  | 16 => embedPair2542 nodeJet2N02703MinusPointP016Rounded2577
  | 17 => embedPair2542 nodeJet2N02703MinusPointP017Rounded2577
  | 18 => embedPair2542 nodeJet2N02703MinusPointP018Rounded2577
  | 19 => embedPair2542 nodeJet2N02703MinusPointP019Rounded2577
  | 20 => embedPair2542 nodeJet2N02703MinusPointP020Rounded2577
  | 21 => embedPair2542 nodeJet2N02703MinusPointP021Rounded2577
  | 22 => embedPair2542 nodeJet2N02703MinusPointP022Rounded2577
  | 23 => embedPair2542 nodeJet2N02703MinusPointP023Rounded2577
  | 24 => embedPair2542 nodeJet2N02703MinusPointP024Rounded2577
  | 25 => embedPair2542 nodeJet2N02703MinusPointP025Rounded2577
  | 26 => embedPair2542 nodeJet2N02703MinusPointP026Rounded2577
  | 27 => embedPair2542 nodeJet2N02703MinusPointP027Rounded2577
  | 28 => embedPair2542 nodeJet2N02703MinusPointP028Rounded2577
  | 29 => embedPair2542 nodeJet2N02703MinusPointP029Rounded2577
  | _ => 0

noncomputable def nodeJet2N02703MinusSignedError2577 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => nodeJet2N02703MinusPointP000Radius2577
  | 1 => nodeJet2N02703MinusPointP001Radius2577
  | 2 => nodeJet2N02703MinusPointP002Radius2577
  | 3 => nodeJet2N02703MinusPointP003Radius2577
  | 4 => nodeJet2N02703MinusPointP004Radius2577
  | 5 => nodeJet2N02703MinusPointP005Radius2577
  | 6 => nodeJet2N02703MinusPointP006Radius2577
  | 7 => nodeJet2N02703MinusPointP007Radius2577
  | 8 => nodeJet2N02703MinusPointP008Radius2577
  | 9 => nodeJet2N02703MinusPointP009Radius2577
  | 10 => nodeJet2N02703MinusPointP010Radius2577
  | 11 => nodeJet2N02703MinusPointP011Radius2577
  | 12 => nodeJet2N02703MinusPointP012Radius2577
  | 13 => nodeJet2N02703MinusPointP013Radius2577
  | 14 => nodeJet2N02703MinusPointP014Radius2577
  | 15 => nodeJet2N02703MinusPointP015Radius2577
  | 16 => nodeJet2N02703MinusPointP016Radius2577
  | 17 => nodeJet2N02703MinusPointP017Radius2577
  | 18 => nodeJet2N02703MinusPointP018Radius2577
  | 19 => nodeJet2N02703MinusPointP019Radius2577
  | 20 => nodeJet2N02703MinusPointP020Radius2577
  | 21 => nodeJet2N02703MinusPointP021Radius2577
  | 22 => nodeJet2N02703MinusPointP022Radius2577
  | 23 => nodeJet2N02703MinusPointP023Radius2577
  | 24 => nodeJet2N02703MinusPointP024Radius2577
  | 25 => nodeJet2N02703MinusPointP025Radius2577
  | 26 => nodeJet2N02703MinusPointP026Radius2577
  | 27 => nodeJet2N02703MinusPointP027Radius2577
  | 28 => nodeJet2N02703MinusPointP028Radius2577
  | 29 => nodeJet2N02703MinusPointP029Radius2577
  | _ => 0

theorem nodeJet2N02703MinusSignedExpError2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02703MinusPointPosition2577 -
        nodeJet2N02703MinusSignedValue2577 i‖ ≤ nodeJet2N02703MinusSignedError2577 i := by
  fin_cases i
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP000RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP001RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP002RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP003RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP004RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP005RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP006RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP007RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP008RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP009RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP010RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP011RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP012RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP013RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP014RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP015RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP016RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP017RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP018RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP019RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP020RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP021RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP022RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP023RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP024RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP025RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP026RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP027RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP028RoundedError2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP029RoundedError2577

theorem nodeJet2N02703MinusSignedUnitNorm2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02703MinusPointPosition2577‖ ≤ 1
        := by
  fin_cases i
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP000DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP001DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP002DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP003DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP004DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP005DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP006DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP007DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP008DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP009DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP010DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP011DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP012DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP013DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP014DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP015DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP016DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP017DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP018DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP019DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP020DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP021DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP022DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP023DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP024DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP025DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP026DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP027DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP028DerivativeNorm2577
  · simpa only [nodeJet2N02703MinusSignedValue2577, nodeJet2N02703MinusSignedError2577] using
      nodeJet2N02703MinusPointP029DerivativeNorm2577

noncomputable def nodeJet2N02703MinusSignedSum2577 : ℂ := ⟨(((-(((31539285290597 * 10^40
        + 8557908471331288974734204892676981211567) * 10^40
        + 8478234993009047541162774411922907084767) * 10^40
        + 120259564713296327688400819594865368379)) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888)),
    (((((2031735368361 * 10^40
        + 8574612130514077713601923791004295238561) * 10^40
        + 2477547770979424062968432798044944138945) * 10^40
        + 9719704434275498219519677931636594880153) : ℝ) /
        (((177450860423 * 10^40
        + 7321510130185077851573570199319728240522) * 10^40
        + 6081091069315933576369956003987455836199) * 10^40
        + 664932998233037501529828597054346100736))⟩

noncomputable def nodeJet2N02703MinusSignedUpper2577 : ℝ := ((99974707 : ℝ) /
        4000000)

theorem nodeJet2N02703MinusSignedSum_eq2577 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02703MinusSignedValue2577 i) =
      nodeJet2N02703MinusSignedSum2577 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        nodeJet2N02703MinusSignedValue2577,
      nodeJet2N02703MinusSignedSum2577, embedPair2542, nodeJet2N02703MinusPointP000Rounded2577,
      nodeJet2N02703MinusPointP001Rounded2577,
      nodeJet2N02703MinusPointP002Rounded2577,
      nodeJet2N02703MinusPointP003Rounded2577,
      nodeJet2N02703MinusPointP004Rounded2577,
      nodeJet2N02703MinusPointP005Rounded2577,
      nodeJet2N02703MinusPointP006Rounded2577,
      nodeJet2N02703MinusPointP007Rounded2577,
      nodeJet2N02703MinusPointP008Rounded2577,
      nodeJet2N02703MinusPointP009Rounded2577,
      nodeJet2N02703MinusPointP010Rounded2577,
      nodeJet2N02703MinusPointP011Rounded2577,
      nodeJet2N02703MinusPointP012Rounded2577,
      nodeJet2N02703MinusPointP013Rounded2577,
      nodeJet2N02703MinusPointP014Rounded2577,
      nodeJet2N02703MinusPointP015Rounded2577,
      nodeJet2N02703MinusPointP016Rounded2577,
      nodeJet2N02703MinusPointP017Rounded2577,
      nodeJet2N02703MinusPointP018Rounded2577,
      nodeJet2N02703MinusPointP019Rounded2577,
      nodeJet2N02703MinusPointP020Rounded2577,
      nodeJet2N02703MinusPointP021Rounded2577,
      nodeJet2N02703MinusPointP022Rounded2577,
      nodeJet2N02703MinusPointP023Rounded2577,
      nodeJet2N02703MinusPointP024Rounded2577,
      nodeJet2N02703MinusPointP025Rounded2577,
      nodeJet2N02703MinusPointP026Rounded2577,
      nodeJet2N02703MinusPointP027Rounded2577,
      nodeJet2N02703MinusPointP028Rounded2577,
      nodeJet2N02703MinusPointP029Rounded2577, Complex.mul_re, Complex.mul_im]

theorem nodeJet2N02703MinusSignedSum_norm2577 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02703MinusSignedValue2577 i‖ ≤
        ((499873533 :
        ℝ) /
        20000000) := by
  rw [nodeJet2N02703MinusSignedSum_eq2577]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [nodeJet2N02703MinusSignedSum2577]

theorem nodeJet2N02703MinusSignedCharge2577 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02703MinusSignedError2577 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      nodeJet2N02703MinusSignedError2577, nodeJet2N02703MinusPointP000Radius2577,
      nodeJet2N02703MinusPointP001Radius2577,
      nodeJet2N02703MinusPointP002Radius2577,
      nodeJet2N02703MinusPointP003Radius2577,
      nodeJet2N02703MinusPointP004Radius2577,
      nodeJet2N02703MinusPointP005Radius2577,
      nodeJet2N02703MinusPointP006Radius2577,
      nodeJet2N02703MinusPointP007Radius2577,
      nodeJet2N02703MinusPointP008Radius2577,
      nodeJet2N02703MinusPointP009Radius2577,
      nodeJet2N02703MinusPointP010Radius2577,
      nodeJet2N02703MinusPointP011Radius2577,
      nodeJet2N02703MinusPointP012Radius2577,
      nodeJet2N02703MinusPointP013Radius2577,
      nodeJet2N02703MinusPointP014Radius2577,
      nodeJet2N02703MinusPointP015Radius2577,
      nodeJet2N02703MinusPointP016Radius2577,
      nodeJet2N02703MinusPointP017Radius2577,
      nodeJet2N02703MinusPointP018Radius2577,
      nodeJet2N02703MinusPointP019Radius2577,
      nodeJet2N02703MinusPointP020Radius2577,
      nodeJet2N02703MinusPointP021Radius2577,
      nodeJet2N02703MinusPointP022Radius2577,
      nodeJet2N02703MinusPointP023Radius2577,
      nodeJet2N02703MinusPointP024Radius2577,
      nodeJet2N02703MinusPointP025Radius2577,
      nodeJet2N02703MinusPointP026Radius2577,
      nodeJet2N02703MinusPointP027Radius2577,
      nodeJet2N02703MinusPointP028Radius2577,
      nodeJet2N02703MinusPointP029Radius2577]

theorem nodeJet2N02703MinusSignedUpper_le2577 :
    signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 nodeJet2N02703MinusPointPosition2577 ≤ nodeJet2N02703MinusSignedUpper2577
          := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02703MinusPointPosition2577‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02703MinusSignedValue2577 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02703MinusSignedError2577 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (nodeJet2N02703MinusSignedExpError2577
        i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02703MinusPointPosition2577‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (nodeJet2N02703MinusSignedUnitNorm2577 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02703MinusPointPosition2577‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 nodeJet2N02703MinusSignedUpper2577
  linarith [nodeJet2N02703MinusSignedSum_norm2577, nodeJet2N02703MinusSignedCharge2577]

theorem nodeJet2N02703MinusPhysical2577 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        nodeJet2N02703MinusPointPosition2577‖ ≤
      nodeJet2N02703MinusSignedUpper2577 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        nodeJet2N02703MinusPointPosition2577
  exact h.trans nodeJet2N02703MinusSignedUpper_le2577

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.nodeJet2N02703MinusSignedExpError2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02703MinusSignedSum_eq2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02703MinusSignedCharge2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02703MinusSignedUpper_le2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02703MinusPhysical2577
