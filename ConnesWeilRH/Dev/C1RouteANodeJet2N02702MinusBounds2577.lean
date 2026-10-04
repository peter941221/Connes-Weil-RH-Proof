import ConnesWeilRH.Dev.C1RouteANodeJet2N02702Minus2577
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem nodeJet2N02702MinusPoint_triangle2577 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def nodeJet2N02702MinusPointP000Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP000Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02702MinusPointP000RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP000Factor2577
        nodeJet2N02702MinusPointP000Center2577) =
        nodeJet2N02702MinusPointP000Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP000RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP000Rounded2577‖ ≤
          nodeJet2N02702MinusPointP000Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP000Factor2577
      nodeJet2N02702MinusPointP000Center2577)
  rw [nodeJet2N02702MinusPointP000RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP000Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP000Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP000Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP000DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP000Factor2577,
      nodeJet2N02702MinusPointP000Error2577, rounding2542,
      nodeJet2N02702MinusPointP000Radius2577]

theorem nodeJet2N02702MinusPointP000DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP000Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP000RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP000Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP000Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP000Rounded2577]

def nodeJet2N02702MinusPointP001Rounded2577 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP001Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP001RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP001Factor2577
        nodeJet2N02702MinusPointP001Center2577) =
        nodeJet2N02702MinusPointP001Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP001RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP001Rounded2577‖ ≤
          nodeJet2N02702MinusPointP001Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP001Factor2577
      nodeJet2N02702MinusPointP001Center2577)
  rw [nodeJet2N02702MinusPointP001RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP001Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP001Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP001Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP001DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP001Factor2577,
      nodeJet2N02702MinusPointP001Error2577, rounding2542,
      nodeJet2N02702MinusPointP001Radius2577]

theorem nodeJet2N02702MinusPointP001DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP001Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP001RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP001Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP001Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP001Rounded2577]

def nodeJet2N02702MinusPointP002Rounded2577 : RatPair2542 :=
  (((33547209 : ℚ) /
        1267650600228229401496703205376),
    (((-659449) : ℚ) /
        39614081257132168796771975168))

noncomputable def nodeJet2N02702MinusPointP002Radius2577 : ℝ := ((1099511702977 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02702MinusPointP002RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP002Factor2577
        nodeJet2N02702MinusPointP002Center2577) =
        nodeJet2N02702MinusPointP002Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP002RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP002Rounded2577‖ ≤
          nodeJet2N02702MinusPointP002Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP002Factor2577
      nodeJet2N02702MinusPointP002Center2577)
  rw [nodeJet2N02702MinusPointP002RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP002Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP002Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP002Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP002DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP002Factor2577,
      nodeJet2N02702MinusPointP002Error2577, rounding2542,
      nodeJet2N02702MinusPointP002Radius2577]

theorem nodeJet2N02702MinusPointP002DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP002Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP002RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP002Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP002Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP002Rounded2577]

def nodeJet2N02702MinusPointP003Rounded2577 : RatPair2542 :=
  (((20780926281095 : ℚ) /
        79228162514264337593543950336),
    ((63081360078583 : ℚ) /
        633825300114114700748351602688))

noncomputable def nodeJet2N02702MinusPointP003Radius2577 : ℝ := ((3933340788583 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP003RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP003Factor2577
        nodeJet2N02702MinusPointP003Center2577) =
        nodeJet2N02702MinusPointP003Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP003RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP003Rounded2577‖ ≤
          nodeJet2N02702MinusPointP003Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP003Factor2577
      nodeJet2N02702MinusPointP003Center2577)
  rw [nodeJet2N02702MinusPointP003RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP003Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP003Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP003Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP003DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP003Factor2577,
      nodeJet2N02702MinusPointP003Error2577, rounding2542,
      nodeJet2N02702MinusPointP003Radius2577]

theorem nodeJet2N02702MinusPointP003DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP003Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP003RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP003Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP003Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP003Rounded2577]

def nodeJet2N02702MinusPointP004Rounded2577 : RatPair2542 :=
  (((61725430500066427 : ℚ) /
        633825300114114700748351602688),
    (((-103767984791520871) : ℚ) /
        1267650600228229401496703205376))

noncomputable def nodeJet2N02702MinusPointP004Radius2577 : ℝ := ((697860081074977 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP004RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP004Factor2577
        nodeJet2N02702MinusPointP004Center2577) =
        nodeJet2N02702MinusPointP004Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP004RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP004Rounded2577‖ ≤
          nodeJet2N02702MinusPointP004Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP004Factor2577
      nodeJet2N02702MinusPointP004Center2577)
  rw [nodeJet2N02702MinusPointP004RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP004Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP004Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP004Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP004DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP004Factor2577,
      nodeJet2N02702MinusPointP004Error2577, rounding2542,
      nodeJet2N02702MinusPointP004Radius2577]

theorem nodeJet2N02702MinusPointP004DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP004Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP004RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP004Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP004Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP004Rounded2577]

def nodeJet2N02702MinusPointP005Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP005Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02702MinusPointP005RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP005Factor2577
        nodeJet2N02702MinusPointP005Center2577) =
        nodeJet2N02702MinusPointP005Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP005RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP005Rounded2577‖ ≤
          nodeJet2N02702MinusPointP005Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP005Factor2577
      nodeJet2N02702MinusPointP005Center2577)
  rw [nodeJet2N02702MinusPointP005RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP005Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP005Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP005Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP005DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP005Factor2577,
      nodeJet2N02702MinusPointP005Error2577, rounding2542,
      nodeJet2N02702MinusPointP005Radius2577]

theorem nodeJet2N02702MinusPointP005DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP005Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP005RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP005Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP005Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP005Rounded2577]

def nodeJet2N02702MinusPointP006Rounded2577 : RatPair2542 :=
  (((25 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP006Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP006RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP006Factor2577
        nodeJet2N02702MinusPointP006Center2577) =
        nodeJet2N02702MinusPointP006Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP006RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP006Rounded2577‖ ≤
          nodeJet2N02702MinusPointP006Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP006Factor2577
      nodeJet2N02702MinusPointP006Center2577)
  rw [nodeJet2N02702MinusPointP006RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP006Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP006Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP006Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP006DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP006Factor2577,
      nodeJet2N02702MinusPointP006Error2577, rounding2542,
      nodeJet2N02702MinusPointP006Radius2577]

theorem nodeJet2N02702MinusPointP006DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP006Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP006RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP006Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP006Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP006Rounded2577]

def nodeJet2N02702MinusPointP007Rounded2577 : RatPair2542 :=
  (((9027432613119 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP007Radius2577 : ℝ := ((275502441029 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem nodeJet2N02702MinusPointP007RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP007Factor2577
        nodeJet2N02702MinusPointP007Center2577) =
        nodeJet2N02702MinusPointP007Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP007RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP007Rounded2577‖ ≤
          nodeJet2N02702MinusPointP007Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP007Factor2577
      nodeJet2N02702MinusPointP007Center2577)
  rw [nodeJet2N02702MinusPointP007RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP007Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP007Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP007Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP007DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP007Factor2577,
      nodeJet2N02702MinusPointP007Error2577, rounding2542,
      nodeJet2N02702MinusPointP007Radius2577]

theorem nodeJet2N02702MinusPointP007DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP007Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP007RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP007Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP007Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP007Rounded2577]

def nodeJet2N02702MinusPointP008Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP008Radius2577 : ℝ := ((549779781741 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02702MinusPointP008RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP008Factor2577
        nodeJet2N02702MinusPointP008Center2577) =
        nodeJet2N02702MinusPointP008Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP008RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP008Rounded2577‖ ≤
          nodeJet2N02702MinusPointP008Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP008Factor2577
      nodeJet2N02702MinusPointP008Center2577)
  rw [nodeJet2N02702MinusPointP008RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP008Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP008Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP008Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP008DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP008Factor2577,
      nodeJet2N02702MinusPointP008Error2577, rounding2542,
      nodeJet2N02702MinusPointP008Radius2577]

theorem nodeJet2N02702MinusPointP008DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP008Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP008RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP008Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP008Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP008Rounded2577]

def nodeJet2N02702MinusPointP009Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP009Radius2577 : ℝ := ((1099559563575 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02702MinusPointP009RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP009Factor2577
        nodeJet2N02702MinusPointP009Center2577) =
        nodeJet2N02702MinusPointP009Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP009RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP009Rounded2577‖ ≤
          nodeJet2N02702MinusPointP009Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP009Factor2577
      nodeJet2N02702MinusPointP009Center2577)
  rw [nodeJet2N02702MinusPointP009RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP009Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP009Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP009Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP009DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP009Factor2577,
      nodeJet2N02702MinusPointP009Error2577, rounding2542,
      nodeJet2N02702MinusPointP009Radius2577]

theorem nodeJet2N02702MinusPointP009DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP009Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP009RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP009Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP009Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP009Rounded2577]

def nodeJet2N02702MinusPointP010Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP010Radius2577 : ℝ := ((1099559563629 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02702MinusPointP010RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP010Factor2577
        nodeJet2N02702MinusPointP010Center2577) =
        nodeJet2N02702MinusPointP010Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP010RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP010Rounded2577‖ ≤
          nodeJet2N02702MinusPointP010Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP010Factor2577
      nodeJet2N02702MinusPointP010Center2577)
  rw [nodeJet2N02702MinusPointP010RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP010Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP010Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP010Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP010DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP010Factor2577,
      nodeJet2N02702MinusPointP010Error2577, rounding2542,
      nodeJet2N02702MinusPointP010Radius2577]

theorem nodeJet2N02702MinusPointP010DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP010Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP010RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP010Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP010Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP010Rounded2577]

def nodeJet2N02702MinusPointP011Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP011Radius2577 : ℝ := ((1099559563665 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02702MinusPointP011RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP011Factor2577
        nodeJet2N02702MinusPointP011Center2577) =
        nodeJet2N02702MinusPointP011Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP011RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP011Rounded2577‖ ≤
          nodeJet2N02702MinusPointP011Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP011Factor2577
      nodeJet2N02702MinusPointP011Center2577)
  rw [nodeJet2N02702MinusPointP011RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP011Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP011Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP011Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP011DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP011Factor2577,
      nodeJet2N02702MinusPointP011Error2577, rounding2542,
      nodeJet2N02702MinusPointP011Radius2577]

theorem nodeJet2N02702MinusPointP011DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP011Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP011RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP011Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP011Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP011Rounded2577]

def nodeJet2N02702MinusPointP012Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP012Radius2577 : ℝ := ((2199119127405 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP012RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP012Factor2577
        nodeJet2N02702MinusPointP012Center2577) =
        nodeJet2N02702MinusPointP012Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP012RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP012Rounded2577‖ ≤
          nodeJet2N02702MinusPointP012Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP012Factor2577
      nodeJet2N02702MinusPointP012Center2577)
  rw [nodeJet2N02702MinusPointP012RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP012Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP012Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP012Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP012DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP012Factor2577,
      nodeJet2N02702MinusPointP012Error2577, rounding2542,
      nodeJet2N02702MinusPointP012Radius2577]

theorem nodeJet2N02702MinusPointP012DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP012Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP012RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP012Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP012Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP012Rounded2577]

def nodeJet2N02702MinusPointP013Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP013Radius2577 : ℝ := ((2199119127473 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP013RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP013Factor2577
        nodeJet2N02702MinusPointP013Center2577) =
        nodeJet2N02702MinusPointP013Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP013RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP013Rounded2577‖ ≤
          nodeJet2N02702MinusPointP013Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP013Factor2577
      nodeJet2N02702MinusPointP013Center2577)
  rw [nodeJet2N02702MinusPointP013RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP013Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP013Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP013Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP013DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP013Factor2577,
      nodeJet2N02702MinusPointP013Error2577, rounding2542,
      nodeJet2N02702MinusPointP013Radius2577]

theorem nodeJet2N02702MinusPointP013DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP013Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP013RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP013Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP013Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP013Rounded2577]

def nodeJet2N02702MinusPointP014Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP014Radius2577 : ℝ := ((1099559563799 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02702MinusPointP014RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP014Factor2577
        nodeJet2N02702MinusPointP014Center2577) =
        nodeJet2N02702MinusPointP014Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP014RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP014Rounded2577‖ ≤
          nodeJet2N02702MinusPointP014Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP014Factor2577
      nodeJet2N02702MinusPointP014Center2577)
  rw [nodeJet2N02702MinusPointP014RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP014Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP014Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP014Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP014DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP014Factor2577,
      nodeJet2N02702MinusPointP014Error2577, rounding2542,
      nodeJet2N02702MinusPointP014Radius2577]

theorem nodeJet2N02702MinusPointP014DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP014Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP014RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP014Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP014Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP014Rounded2577]

def nodeJet2N02702MinusPointP015Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP015Radius2577 : ℝ := ((2199119127689 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP015RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP015Factor2577
        nodeJet2N02702MinusPointP015Center2577) =
        nodeJet2N02702MinusPointP015Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP015RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP015Rounded2577‖ ≤
          nodeJet2N02702MinusPointP015Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP015Factor2577
      nodeJet2N02702MinusPointP015Center2577)
  rw [nodeJet2N02702MinusPointP015RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP015Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP015Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP015Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP015DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP015Factor2577,
      nodeJet2N02702MinusPointP015Error2577, rounding2542,
      nodeJet2N02702MinusPointP015Radius2577]

theorem nodeJet2N02702MinusPointP015DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP015Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP015RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP015Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP015Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP015Rounded2577]

def nodeJet2N02702MinusPointP016Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP016Radius2577 : ℝ := ((1099559563877 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02702MinusPointP016RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP016Factor2577
        nodeJet2N02702MinusPointP016Center2577) =
        nodeJet2N02702MinusPointP016Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP016RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP016Rounded2577‖ ≤
          nodeJet2N02702MinusPointP016Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP016Factor2577
      nodeJet2N02702MinusPointP016Center2577)
  rw [nodeJet2N02702MinusPointP016RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP016Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP016Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP016Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP016DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP016Factor2577,
      nodeJet2N02702MinusPointP016Error2577, rounding2542,
      nodeJet2N02702MinusPointP016Radius2577]

theorem nodeJet2N02702MinusPointP016DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP016Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP016RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP016Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP016Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP016Rounded2577]

def nodeJet2N02702MinusPointP017Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP017Radius2577 : ℝ := ((274889890985 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem nodeJet2N02702MinusPointP017RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP017Factor2577
        nodeJet2N02702MinusPointP017Center2577) =
        nodeJet2N02702MinusPointP017Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP017RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP017Rounded2577‖ ≤
          nodeJet2N02702MinusPointP017Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP017Factor2577
      nodeJet2N02702MinusPointP017Center2577)
  rw [nodeJet2N02702MinusPointP017RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP017Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP017Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP017Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP017DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP017Factor2577,
      nodeJet2N02702MinusPointP017Error2577, rounding2542,
      nodeJet2N02702MinusPointP017Radius2577]

theorem nodeJet2N02702MinusPointP017DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP017Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP017RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP017Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP017Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP017Rounded2577]

def nodeJet2N02702MinusPointP018Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP018Radius2577 : ℝ := ((274889890991 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem nodeJet2N02702MinusPointP018RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP018Factor2577
        nodeJet2N02702MinusPointP018Center2577) =
        nodeJet2N02702MinusPointP018Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP018RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP018Rounded2577‖ ≤
          nodeJet2N02702MinusPointP018Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP018Factor2577
      nodeJet2N02702MinusPointP018Center2577)
  rw [nodeJet2N02702MinusPointP018RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP018Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP018Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP018Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP018DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP018Factor2577,
      nodeJet2N02702MinusPointP018Error2577, rounding2542,
      nodeJet2N02702MinusPointP018Radius2577]

theorem nodeJet2N02702MinusPointP018DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP018Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP018RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP018Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP018Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP018Rounded2577]

def nodeJet2N02702MinusPointP019Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP019Radius2577 : ℝ := ((2199119128015 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP019RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP019Factor2577
        nodeJet2N02702MinusPointP019Center2577) =
        nodeJet2N02702MinusPointP019Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP019RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP019Rounded2577‖ ≤
          nodeJet2N02702MinusPointP019Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP019Factor2577
      nodeJet2N02702MinusPointP019Center2577)
  rw [nodeJet2N02702MinusPointP019RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP019Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP019Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP019Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP019DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP019Factor2577,
      nodeJet2N02702MinusPointP019Error2577, rounding2542,
      nodeJet2N02702MinusPointP019Radius2577]

theorem nodeJet2N02702MinusPointP019DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP019Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP019RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP019Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP019Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP019Rounded2577]

def nodeJet2N02702MinusPointP020Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP020Radius2577 : ℝ := ((2199119128109 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP020RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP020Factor2577
        nodeJet2N02702MinusPointP020Center2577) =
        nodeJet2N02702MinusPointP020Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP020RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP020Rounded2577‖ ≤
          nodeJet2N02702MinusPointP020Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP020Factor2577
      nodeJet2N02702MinusPointP020Center2577)
  rw [nodeJet2N02702MinusPointP020RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP020Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP020Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP020Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP020DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP020Factor2577,
      nodeJet2N02702MinusPointP020Error2577, rounding2542,
      nodeJet2N02702MinusPointP020Radius2577]

theorem nodeJet2N02702MinusPointP020DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP020Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP020RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP020Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP020Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP020Rounded2577]

def nodeJet2N02702MinusPointP021Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP021Radius2577 : ℝ := ((2199119128187 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP021RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP021Factor2577
        nodeJet2N02702MinusPointP021Center2577) =
        nodeJet2N02702MinusPointP021Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP021RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP021Rounded2577‖ ≤
          nodeJet2N02702MinusPointP021Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP021Factor2577
      nodeJet2N02702MinusPointP021Center2577)
  rw [nodeJet2N02702MinusPointP021RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP021Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP021Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP021Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP021DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP021Factor2577,
      nodeJet2N02702MinusPointP021Error2577, rounding2542,
      nodeJet2N02702MinusPointP021Radius2577]

theorem nodeJet2N02702MinusPointP021DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP021Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP021RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP021Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP021Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP021Rounded2577]

def nodeJet2N02702MinusPointP022Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP022Radius2577 : ℝ := ((2199119128227 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP022RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP022Factor2577
        nodeJet2N02702MinusPointP022Center2577) =
        nodeJet2N02702MinusPointP022Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP022RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP022Rounded2577‖ ≤
          nodeJet2N02702MinusPointP022Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP022Factor2577
      nodeJet2N02702MinusPointP022Center2577)
  rw [nodeJet2N02702MinusPointP022RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP022Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP022Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP022Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP022DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP022Factor2577,
      nodeJet2N02702MinusPointP022Error2577, rounding2542,
      nodeJet2N02702MinusPointP022Radius2577]

theorem nodeJet2N02702MinusPointP022DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP022Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP022RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP022Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP022Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP022Rounded2577]

def nodeJet2N02702MinusPointP023Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP023Radius2577 : ℝ := ((2199119128343 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP023RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP023Factor2577
        nodeJet2N02702MinusPointP023Center2577) =
        nodeJet2N02702MinusPointP023Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP023RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP023Rounded2577‖ ≤
          nodeJet2N02702MinusPointP023Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP023Factor2577
      nodeJet2N02702MinusPointP023Center2577)
  rw [nodeJet2N02702MinusPointP023RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP023Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP023Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP023Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP023DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP023Factor2577,
      nodeJet2N02702MinusPointP023Error2577, rounding2542,
      nodeJet2N02702MinusPointP023Radius2577]

theorem nodeJet2N02702MinusPointP023DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP023Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP023RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP023Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP023Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP023Rounded2577]

def nodeJet2N02702MinusPointP024Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP024Radius2577 : ℝ := ((549779782099 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02702MinusPointP024RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP024Factor2577
        nodeJet2N02702MinusPointP024Center2577) =
        nodeJet2N02702MinusPointP024Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP024RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP024Rounded2577‖ ≤
          nodeJet2N02702MinusPointP024Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP024Factor2577
      nodeJet2N02702MinusPointP024Center2577)
  rw [nodeJet2N02702MinusPointP024RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP024Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP024Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP024Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP024DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP024Factor2577,
      nodeJet2N02702MinusPointP024Error2577, rounding2542,
      nodeJet2N02702MinusPointP024Radius2577]

theorem nodeJet2N02702MinusPointP024DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP024Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP024RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP024Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP024Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP024Rounded2577]

def nodeJet2N02702MinusPointP025Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP025Radius2577 : ℝ := ((2199119128463 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP025RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP025Factor2577
        nodeJet2N02702MinusPointP025Center2577) =
        nodeJet2N02702MinusPointP025Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP025RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP025Rounded2577‖ ≤
          nodeJet2N02702MinusPointP025Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP025Factor2577
      nodeJet2N02702MinusPointP025Center2577)
  rw [nodeJet2N02702MinusPointP025RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP025Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP025Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP025Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP025DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP025Factor2577,
      nodeJet2N02702MinusPointP025Error2577, rounding2542,
      nodeJet2N02702MinusPointP025Radius2577]

theorem nodeJet2N02702MinusPointP025DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP025Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP025RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP025Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP025Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP025Rounded2577]

def nodeJet2N02702MinusPointP026Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP026Radius2577 : ℝ := ((2199119128531 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP026RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP026Factor2577
        nodeJet2N02702MinusPointP026Center2577) =
        nodeJet2N02702MinusPointP026Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP026RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP026Rounded2577‖ ≤
          nodeJet2N02702MinusPointP026Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP026Factor2577
      nodeJet2N02702MinusPointP026Center2577)
  rw [nodeJet2N02702MinusPointP026RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP026Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP026Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP026Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP026DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP026Factor2577,
      nodeJet2N02702MinusPointP026Error2577, rounding2542,
      nodeJet2N02702MinusPointP026Radius2577]

theorem nodeJet2N02702MinusPointP026DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP026Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP026RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP026Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP026Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP026Rounded2577]

def nodeJet2N02702MinusPointP027Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP027Radius2577 : ℝ := ((2199119128629 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02702MinusPointP027RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP027Factor2577
        nodeJet2N02702MinusPointP027Center2577) =
        nodeJet2N02702MinusPointP027Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP027RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP027Rounded2577‖ ≤
          nodeJet2N02702MinusPointP027Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP027Factor2577
      nodeJet2N02702MinusPointP027Center2577)
  rw [nodeJet2N02702MinusPointP027RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP027Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP027Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP027Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP027DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP027Factor2577,
      nodeJet2N02702MinusPointP027Error2577, rounding2542,
      nodeJet2N02702MinusPointP027Radius2577]

theorem nodeJet2N02702MinusPointP027DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP027Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP027RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP027Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP027Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP027Rounded2577]

def nodeJet2N02702MinusPointP028Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP028Radius2577 : ℝ := ((549779782167 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02702MinusPointP028RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP028Factor2577
        nodeJet2N02702MinusPointP028Center2577) =
        nodeJet2N02702MinusPointP028Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP028RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP028Rounded2577‖ ≤
          nodeJet2N02702MinusPointP028Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP028Factor2577
      nodeJet2N02702MinusPointP028Center2577)
  rw [nodeJet2N02702MinusPointP028RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP028Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP028Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP028Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP028DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP028Factor2577,
      nodeJet2N02702MinusPointP028Error2577, rounding2542,
      nodeJet2N02702MinusPointP028Radius2577]

theorem nodeJet2N02702MinusPointP028DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP028Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP028RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP028Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP028Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP028Rounded2577]

def nodeJet2N02702MinusPointP029Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02702MinusPointP029Radius2577 : ℝ := ((274889891091 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem nodeJet2N02702MinusPointP029RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02702MinusPointP029Factor2577
        nodeJet2N02702MinusPointP029Center2577) =
        nodeJet2N02702MinusPointP029Rounded2577 := by
  cbv

theorem nodeJet2N02702MinusPointP029RoundedError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02702MinusPointPosition2577 -
      embedPair2542 nodeJet2N02702MinusPointP029Rounded2577‖ ≤
          nodeJet2N02702MinusPointP029Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02702MinusPointP029Factor2577
      nodeJet2N02702MinusPointP029Center2577)
  rw [nodeJet2N02702MinusPointP029RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP029Factor2577 * embedPair2542
        nodeJet2N02702MinusPointP029Center2577)
    (embedPair2542 nodeJet2N02702MinusPointP029Rounded2577)).trans (add_le_add
        nodeJet2N02702MinusPointP029DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02702MinusPointP029Factor2577,
      nodeJet2N02702MinusPointP029Error2577, rounding2542,
      nodeJet2N02702MinusPointP029Radius2577]

theorem nodeJet2N02702MinusPointP029DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02702MinusPointPosition2577‖ ≤ 1 :=
        by
  have h := nodeJet2N02702MinusPoint_triangle2577
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02702MinusPointPosition2577)
    (embedPair2542 nodeJet2N02702MinusPointP029Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02702MinusPointP029RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02702MinusPointP029Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02702MinusPointP029Radius2577, pairMagnitude2542,
      nodeJet2N02702MinusPointP029Rounded2577]

noncomputable def nodeJet2N02702MinusSignedValue2577 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 nodeJet2N02702MinusPointP000Rounded2577
  | 1 => embedPair2542 nodeJet2N02702MinusPointP001Rounded2577
  | 2 => embedPair2542 nodeJet2N02702MinusPointP002Rounded2577
  | 3 => embedPair2542 nodeJet2N02702MinusPointP003Rounded2577
  | 4 => embedPair2542 nodeJet2N02702MinusPointP004Rounded2577
  | 5 => embedPair2542 nodeJet2N02702MinusPointP005Rounded2577
  | 6 => embedPair2542 nodeJet2N02702MinusPointP006Rounded2577
  | 7 => embedPair2542 nodeJet2N02702MinusPointP007Rounded2577
  | 8 => embedPair2542 nodeJet2N02702MinusPointP008Rounded2577
  | 9 => embedPair2542 nodeJet2N02702MinusPointP009Rounded2577
  | 10 => embedPair2542 nodeJet2N02702MinusPointP010Rounded2577
  | 11 => embedPair2542 nodeJet2N02702MinusPointP011Rounded2577
  | 12 => embedPair2542 nodeJet2N02702MinusPointP012Rounded2577
  | 13 => embedPair2542 nodeJet2N02702MinusPointP013Rounded2577
  | 14 => embedPair2542 nodeJet2N02702MinusPointP014Rounded2577
  | 15 => embedPair2542 nodeJet2N02702MinusPointP015Rounded2577
  | 16 => embedPair2542 nodeJet2N02702MinusPointP016Rounded2577
  | 17 => embedPair2542 nodeJet2N02702MinusPointP017Rounded2577
  | 18 => embedPair2542 nodeJet2N02702MinusPointP018Rounded2577
  | 19 => embedPair2542 nodeJet2N02702MinusPointP019Rounded2577
  | 20 => embedPair2542 nodeJet2N02702MinusPointP020Rounded2577
  | 21 => embedPair2542 nodeJet2N02702MinusPointP021Rounded2577
  | 22 => embedPair2542 nodeJet2N02702MinusPointP022Rounded2577
  | 23 => embedPair2542 nodeJet2N02702MinusPointP023Rounded2577
  | 24 => embedPair2542 nodeJet2N02702MinusPointP024Rounded2577
  | 25 => embedPair2542 nodeJet2N02702MinusPointP025Rounded2577
  | 26 => embedPair2542 nodeJet2N02702MinusPointP026Rounded2577
  | 27 => embedPair2542 nodeJet2N02702MinusPointP027Rounded2577
  | 28 => embedPair2542 nodeJet2N02702MinusPointP028Rounded2577
  | 29 => embedPair2542 nodeJet2N02702MinusPointP029Rounded2577
  | _ => 0

noncomputable def nodeJet2N02702MinusSignedError2577 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => nodeJet2N02702MinusPointP000Radius2577
  | 1 => nodeJet2N02702MinusPointP001Radius2577
  | 2 => nodeJet2N02702MinusPointP002Radius2577
  | 3 => nodeJet2N02702MinusPointP003Radius2577
  | 4 => nodeJet2N02702MinusPointP004Radius2577
  | 5 => nodeJet2N02702MinusPointP005Radius2577
  | 6 => nodeJet2N02702MinusPointP006Radius2577
  | 7 => nodeJet2N02702MinusPointP007Radius2577
  | 8 => nodeJet2N02702MinusPointP008Radius2577
  | 9 => nodeJet2N02702MinusPointP009Radius2577
  | 10 => nodeJet2N02702MinusPointP010Radius2577
  | 11 => nodeJet2N02702MinusPointP011Radius2577
  | 12 => nodeJet2N02702MinusPointP012Radius2577
  | 13 => nodeJet2N02702MinusPointP013Radius2577
  | 14 => nodeJet2N02702MinusPointP014Radius2577
  | 15 => nodeJet2N02702MinusPointP015Radius2577
  | 16 => nodeJet2N02702MinusPointP016Radius2577
  | 17 => nodeJet2N02702MinusPointP017Radius2577
  | 18 => nodeJet2N02702MinusPointP018Radius2577
  | 19 => nodeJet2N02702MinusPointP019Radius2577
  | 20 => nodeJet2N02702MinusPointP020Radius2577
  | 21 => nodeJet2N02702MinusPointP021Radius2577
  | 22 => nodeJet2N02702MinusPointP022Radius2577
  | 23 => nodeJet2N02702MinusPointP023Radius2577
  | 24 => nodeJet2N02702MinusPointP024Radius2577
  | 25 => nodeJet2N02702MinusPointP025Radius2577
  | 26 => nodeJet2N02702MinusPointP026Radius2577
  | 27 => nodeJet2N02702MinusPointP027Radius2577
  | 28 => nodeJet2N02702MinusPointP028Radius2577
  | 29 => nodeJet2N02702MinusPointP029Radius2577
  | _ => 0

theorem nodeJet2N02702MinusSignedExpError2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02702MinusPointPosition2577 -
        nodeJet2N02702MinusSignedValue2577 i‖ ≤ nodeJet2N02702MinusSignedError2577 i := by
  fin_cases i
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP000RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP001RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP002RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP003RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP004RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP005RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP006RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP007RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP008RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP009RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP010RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP011RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP012RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP013RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP014RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP015RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP016RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP017RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP018RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP019RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP020RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP021RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP022RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP023RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP024RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP025RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP026RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP027RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP028RoundedError2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP029RoundedError2577

theorem nodeJet2N02702MinusSignedUnitNorm2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02702MinusPointPosition2577‖ ≤ 1
        := by
  fin_cases i
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP000DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP001DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP002DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP003DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP004DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP005DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP006DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP007DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP008DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP009DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP010DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP011DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP012DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP013DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP014DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP015DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP016DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP017DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP018DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP019DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP020DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP021DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP022DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP023DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP024DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP025DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP026DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP027DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP028DerivativeNorm2577
  · simpa only [nodeJet2N02702MinusSignedValue2577, nodeJet2N02702MinusSignedError2577] using
      nodeJet2N02702MinusPointP029DerivativeNorm2577

noncomputable def nodeJet2N02702MinusSignedSum2577 : ℂ := ⟨(((-(((16023924430353 * 10^40
        + 5242071933091173556282372115792106864188) * 10^40
        + 9328908203764146563402809135374403296283) * 10^40
        + 3649445089198445817593826108795188287511)) : ℝ) /
        (((709803441694 * 10^40
        + 9286040520740311406294280797278912962090) * 10^40
        + 4324364277263734305479824015949823344796) * 10^40
        + 2659731992932150006119314388217384402944)),
    (((((14515851551141 * 10^40
        + 6884032664289221361995672799949038470726) * 10^40
        + 2286707942877801821868240942675235114449) * 10^40
        + 2454130966629506773303445113386718849447) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888))⟩

noncomputable def nodeJet2N02702MinusSignedUpper2577 : ℝ := ((1239146591 : ℝ) /
        50000000)

theorem nodeJet2N02702MinusSignedSum_eq2577 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02702MinusSignedValue2577 i) =
      nodeJet2N02702MinusSignedSum2577 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        nodeJet2N02702MinusSignedValue2577,
      nodeJet2N02702MinusSignedSum2577, embedPair2542, nodeJet2N02702MinusPointP000Rounded2577,
      nodeJet2N02702MinusPointP001Rounded2577,
      nodeJet2N02702MinusPointP002Rounded2577,
      nodeJet2N02702MinusPointP003Rounded2577,
      nodeJet2N02702MinusPointP004Rounded2577,
      nodeJet2N02702MinusPointP005Rounded2577,
      nodeJet2N02702MinusPointP006Rounded2577,
      nodeJet2N02702MinusPointP007Rounded2577,
      nodeJet2N02702MinusPointP008Rounded2577,
      nodeJet2N02702MinusPointP009Rounded2577,
      nodeJet2N02702MinusPointP010Rounded2577,
      nodeJet2N02702MinusPointP011Rounded2577,
      nodeJet2N02702MinusPointP012Rounded2577,
      nodeJet2N02702MinusPointP013Rounded2577,
      nodeJet2N02702MinusPointP014Rounded2577,
      nodeJet2N02702MinusPointP015Rounded2577,
      nodeJet2N02702MinusPointP016Rounded2577,
      nodeJet2N02702MinusPointP017Rounded2577,
      nodeJet2N02702MinusPointP018Rounded2577,
      nodeJet2N02702MinusPointP019Rounded2577,
      nodeJet2N02702MinusPointP020Rounded2577,
      nodeJet2N02702MinusPointP021Rounded2577,
      nodeJet2N02702MinusPointP022Rounded2577,
      nodeJet2N02702MinusPointP023Rounded2577,
      nodeJet2N02702MinusPointP024Rounded2577,
      nodeJet2N02702MinusPointP025Rounded2577,
      nodeJet2N02702MinusPointP026Rounded2577,
      nodeJet2N02702MinusPointP027Rounded2577,
      nodeJet2N02702MinusPointP028Rounded2577,
      nodeJet2N02702MinusPointP029Rounded2577, Complex.mul_re, Complex.mul_im]

theorem nodeJet2N02702MinusSignedSum_norm2577 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02702MinusSignedValue2577 i‖ ≤
        ((619573293 :
        ℝ) /
        25000000) := by
  rw [nodeJet2N02702MinusSignedSum_eq2577]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [nodeJet2N02702MinusSignedSum2577]

theorem nodeJet2N02702MinusSignedCharge2577 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02702MinusSignedError2577 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      nodeJet2N02702MinusSignedError2577, nodeJet2N02702MinusPointP000Radius2577,
      nodeJet2N02702MinusPointP001Radius2577,
      nodeJet2N02702MinusPointP002Radius2577,
      nodeJet2N02702MinusPointP003Radius2577,
      nodeJet2N02702MinusPointP004Radius2577,
      nodeJet2N02702MinusPointP005Radius2577,
      nodeJet2N02702MinusPointP006Radius2577,
      nodeJet2N02702MinusPointP007Radius2577,
      nodeJet2N02702MinusPointP008Radius2577,
      nodeJet2N02702MinusPointP009Radius2577,
      nodeJet2N02702MinusPointP010Radius2577,
      nodeJet2N02702MinusPointP011Radius2577,
      nodeJet2N02702MinusPointP012Radius2577,
      nodeJet2N02702MinusPointP013Radius2577,
      nodeJet2N02702MinusPointP014Radius2577,
      nodeJet2N02702MinusPointP015Radius2577,
      nodeJet2N02702MinusPointP016Radius2577,
      nodeJet2N02702MinusPointP017Radius2577,
      nodeJet2N02702MinusPointP018Radius2577,
      nodeJet2N02702MinusPointP019Radius2577,
      nodeJet2N02702MinusPointP020Radius2577,
      nodeJet2N02702MinusPointP021Radius2577,
      nodeJet2N02702MinusPointP022Radius2577,
      nodeJet2N02702MinusPointP023Radius2577,
      nodeJet2N02702MinusPointP024Radius2577,
      nodeJet2N02702MinusPointP025Radius2577,
      nodeJet2N02702MinusPointP026Radius2577,
      nodeJet2N02702MinusPointP027Radius2577,
      nodeJet2N02702MinusPointP028Radius2577,
      nodeJet2N02702MinusPointP029Radius2577]

theorem nodeJet2N02702MinusSignedUpper_le2577 :
    signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 nodeJet2N02702MinusPointPosition2577 ≤ nodeJet2N02702MinusSignedUpper2577
          := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02702MinusPointPosition2577‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02702MinusSignedValue2577 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02702MinusSignedError2577 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (nodeJet2N02702MinusSignedExpError2577
        i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02702MinusPointPosition2577‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (nodeJet2N02702MinusSignedUnitNorm2577 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i nodeJet2N02702MinusPointPosition2577‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 nodeJet2N02702MinusSignedUpper2577
  linarith [nodeJet2N02702MinusSignedSum_norm2577, nodeJet2N02702MinusSignedCharge2577]

theorem nodeJet2N02702MinusPhysical2577 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        nodeJet2N02702MinusPointPosition2577‖ ≤
      nodeJet2N02702MinusSignedUpper2577 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        nodeJet2N02702MinusPointPosition2577
  exact h.trans nodeJet2N02702MinusSignedUpper_le2577

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.nodeJet2N02702MinusSignedExpError2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02702MinusSignedSum_eq2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02702MinusSignedCharge2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02702MinusSignedUpper_le2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02702MinusPhysical2577
