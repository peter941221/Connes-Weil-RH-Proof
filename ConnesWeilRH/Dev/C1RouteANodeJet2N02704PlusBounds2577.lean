import ConnesWeilRH.Dev.C1RouteANodeJet2N02704Plus2577
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem nodeJet2N02704PlusPoint_triangle2577 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def nodeJet2N02704PlusPointP000Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP000Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02704PlusPointP000RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP000Factor2577
        nodeJet2N02704PlusPointP000Center2577) =
        nodeJet2N02704PlusPointP000Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP000RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP000Rounded2577‖ ≤
          nodeJet2N02704PlusPointP000Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP000Factor2577
      nodeJet2N02704PlusPointP000Center2577)
  rw [nodeJet2N02704PlusPointP000RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP000Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP000Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP000Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP000DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP000Factor2577,
      nodeJet2N02704PlusPointP000Error2577, rounding2542,
      nodeJet2N02704PlusPointP000Radius2577]

theorem nodeJet2N02704PlusPointP000DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP000Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP000RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP000Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP000Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP000Rounded2577]

def nodeJet2N02704PlusPointP001Rounded2577 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP001Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704PlusPointP001RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP001Factor2577
        nodeJet2N02704PlusPointP001Center2577) =
        nodeJet2N02704PlusPointP001Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP001RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP001Rounded2577‖ ≤
          nodeJet2N02704PlusPointP001Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP001Factor2577
      nodeJet2N02704PlusPointP001Center2577)
  rw [nodeJet2N02704PlusPointP001RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP001Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP001Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP001Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP001DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP001Factor2577,
      nodeJet2N02704PlusPointP001Error2577, rounding2542,
      nodeJet2N02704PlusPointP001Radius2577]

theorem nodeJet2N02704PlusPointP001DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP001Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP001RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP001Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP001Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP001Rounded2577]

def nodeJet2N02704PlusPointP002Rounded2577 : RatPair2542 :=
  (((903879 : ℚ) /
        633825300114114700748351602688),
    (((-236065) : ℚ) /
        316912650057057350374175801344))

noncomputable def nodeJet2N02704PlusPointP002Radius2577 : ℝ := ((2199023263623 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704PlusPointP002RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP002Factor2577
        nodeJet2N02704PlusPointP002Center2577) =
        nodeJet2N02704PlusPointP002Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP002RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP002Rounded2577‖ ≤
          nodeJet2N02704PlusPointP002Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP002Factor2577
      nodeJet2N02704PlusPointP002Center2577)
  rw [nodeJet2N02704PlusPointP002RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP002Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP002Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP002Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP002DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP002Factor2577,
      nodeJet2N02704PlusPointP002Error2577, rounding2542,
      nodeJet2N02704PlusPointP002Radius2577]

theorem nodeJet2N02704PlusPointP002DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP002Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP002RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP002Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP002Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP002Rounded2577]

def nodeJet2N02704PlusPointP003Rounded2577 : RatPair2542 :=
  (((7753502047715 : ℚ) /
        633825300114114700748351602688),
    ((216351432037 : ℚ) /
        39614081257132168796771975168))

noncomputable def nodeJet2N02704PlusPointP003Radius2577 : ℝ := ((1142060792479 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704PlusPointP003RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP003Factor2577
        nodeJet2N02704PlusPointP003Center2577) =
        nodeJet2N02704PlusPointP003Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP003RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP003Rounded2577‖ ≤
          nodeJet2N02704PlusPointP003Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP003Factor2577
      nodeJet2N02704PlusPointP003Center2577)
  rw [nodeJet2N02704PlusPointP003RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP003Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP003Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP003Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP003DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP003Factor2577,
      nodeJet2N02704PlusPointP003Error2577, rounding2542,
      nodeJet2N02704PlusPointP003Radius2577]

theorem nodeJet2N02704PlusPointP003DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP003Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP003RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP003Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP003Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP003Rounded2577]

def nodeJet2N02704PlusPointP004Rounded2577 : RatPair2542 :=
  (((2745659278719493 : ℚ) /
        633825300114114700748351602688),
    (((-5125142618310593) : ℚ) /
        1267650600228229401496703205376))

noncomputable def nodeJet2N02704PlusPointP004Radius2577 : ℝ := ((18050297807575 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704PlusPointP004RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP004Factor2577
        nodeJet2N02704PlusPointP004Center2577) =
        nodeJet2N02704PlusPointP004Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP004RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP004Rounded2577‖ ≤
          nodeJet2N02704PlusPointP004Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP004Factor2577
      nodeJet2N02704PlusPointP004Center2577)
  rw [nodeJet2N02704PlusPointP004RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP004Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP004Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP004Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP004DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP004Factor2577,
      nodeJet2N02704PlusPointP004Error2577, rounding2542,
      nodeJet2N02704PlusPointP004Radius2577]

theorem nodeJet2N02704PlusPointP004DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP004Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP004RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP004Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP004Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP004Rounded2577]

def nodeJet2N02704PlusPointP005Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP005Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02704PlusPointP005RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP005Factor2577
        nodeJet2N02704PlusPointP005Center2577) =
        nodeJet2N02704PlusPointP005Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP005RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP005Rounded2577‖ ≤
          nodeJet2N02704PlusPointP005Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP005Factor2577
      nodeJet2N02704PlusPointP005Center2577)
  rw [nodeJet2N02704PlusPointP005RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP005Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP005Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP005Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP005DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP005Factor2577,
      nodeJet2N02704PlusPointP005Error2577, rounding2542,
      nodeJet2N02704PlusPointP005Radius2577]

theorem nodeJet2N02704PlusPointP005DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP005Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP005RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP005Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP005Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP005Rounded2577]

def nodeJet2N02704PlusPointP006Rounded2577 : RatPair2542 :=
  (((5 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP006Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704PlusPointP006RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP006Factor2577
        nodeJet2N02704PlusPointP006Center2577) =
        nodeJet2N02704PlusPointP006Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP006RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP006Rounded2577‖ ≤
          nodeJet2N02704PlusPointP006Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP006Factor2577
      nodeJet2N02704PlusPointP006Center2577)
  rw [nodeJet2N02704PlusPointP006RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP006Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP006Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP006Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP006DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP006Factor2577,
      nodeJet2N02704PlusPointP006Error2577, rounding2542,
      nodeJet2N02704PlusPointP006Radius2577]

theorem nodeJet2N02704PlusPointP006DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP006Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP006RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP006Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP006Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP006Rounded2577]

def nodeJet2N02704PlusPointP007Rounded2577 : RatPair2542 :=
  (((1962994166129 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP007Radius2577 : ℝ := ((1099654075807 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704PlusPointP007RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP007Factor2577
        nodeJet2N02704PlusPointP007Center2577) =
        nodeJet2N02704PlusPointP007Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP007RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP007Rounded2577‖ ≤
          nodeJet2N02704PlusPointP007Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP007Factor2577
      nodeJet2N02704PlusPointP007Center2577)
  rw [nodeJet2N02704PlusPointP007RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP007Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP007Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP007Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP007DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP007Factor2577,
      nodeJet2N02704PlusPointP007Error2577, rounding2542,
      nodeJet2N02704PlusPointP007Radius2577]

theorem nodeJet2N02704PlusPointP007DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP007Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP007RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP007Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP007Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP007Rounded2577]

def nodeJet2N02704PlusPointP008Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP008Radius2577 : ℝ := ((137439327919 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem nodeJet2N02704PlusPointP008RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP008Factor2577
        nodeJet2N02704PlusPointP008Center2577) =
        nodeJet2N02704PlusPointP008Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP008RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP008Rounded2577‖ ≤
          nodeJet2N02704PlusPointP008Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP008Factor2577
      nodeJet2N02704PlusPointP008Center2577)
  rw [nodeJet2N02704PlusPointP008RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP008Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP008Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP008Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP008DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP008Factor2577,
      nodeJet2N02704PlusPointP008Error2577, rounding2542,
      nodeJet2N02704PlusPointP008Radius2577]

theorem nodeJet2N02704PlusPointP008DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP008Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP008RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP008Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP008Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP008Rounded2577]

def nodeJet2N02704PlusPointP009Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP009Radius2577 : ℝ := ((1099514623375 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704PlusPointP009RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP009Factor2577
        nodeJet2N02704PlusPointP009Center2577) =
        nodeJet2N02704PlusPointP009Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP009RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP009Rounded2577‖ ≤
          nodeJet2N02704PlusPointP009Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP009Factor2577
      nodeJet2N02704PlusPointP009Center2577)
  rw [nodeJet2N02704PlusPointP009RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP009Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP009Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP009Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP009DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP009Factor2577,
      nodeJet2N02704PlusPointP009Error2577, rounding2542,
      nodeJet2N02704PlusPointP009Radius2577]

theorem nodeJet2N02704PlusPointP009DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP009Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP009RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP009Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP009Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP009Rounded2577]

def nodeJet2N02704PlusPointP010Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP010Radius2577 : ℝ := ((2199029246777 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704PlusPointP010RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP010Factor2577
        nodeJet2N02704PlusPointP010Center2577) =
        nodeJet2N02704PlusPointP010Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP010RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP010Rounded2577‖ ≤
          nodeJet2N02704PlusPointP010Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP010Factor2577
      nodeJet2N02704PlusPointP010Center2577)
  rw [nodeJet2N02704PlusPointP010RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP010Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP010Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP010Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP010DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP010Factor2577,
      nodeJet2N02704PlusPointP010Error2577, rounding2542,
      nodeJet2N02704PlusPointP010Radius2577]

theorem nodeJet2N02704PlusPointP010DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP010Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP010RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP010Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP010Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP010Rounded2577]

def nodeJet2N02704PlusPointP011Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP011Radius2577 : ℝ := ((2199029246795 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704PlusPointP011RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP011Factor2577
        nodeJet2N02704PlusPointP011Center2577) =
        nodeJet2N02704PlusPointP011Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP011RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP011Rounded2577‖ ≤
          nodeJet2N02704PlusPointP011Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP011Factor2577
      nodeJet2N02704PlusPointP011Center2577)
  rw [nodeJet2N02704PlusPointP011RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP011Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP011Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP011Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP011DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP011Factor2577,
      nodeJet2N02704PlusPointP011Error2577, rounding2542,
      nodeJet2N02704PlusPointP011Radius2577]

theorem nodeJet2N02704PlusPointP011DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP011Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP011RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP011Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP011Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP011Rounded2577]

def nodeJet2N02704PlusPointP012Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP012Radius2577 : ℝ := ((1099514623407 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704PlusPointP012RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP012Factor2577
        nodeJet2N02704PlusPointP012Center2577) =
        nodeJet2N02704PlusPointP012Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP012RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP012Rounded2577‖ ≤
          nodeJet2N02704PlusPointP012Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP012Factor2577
      nodeJet2N02704PlusPointP012Center2577)
  rw [nodeJet2N02704PlusPointP012RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP012Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP012Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP012Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP012DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP012Factor2577,
      nodeJet2N02704PlusPointP012Error2577, rounding2542,
      nodeJet2N02704PlusPointP012Radius2577]

theorem nodeJet2N02704PlusPointP012DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP012Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP012RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP012Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP012Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP012Rounded2577]

def nodeJet2N02704PlusPointP013Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP013Radius2577 : ℝ := ((2199029246831 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704PlusPointP013RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP013Factor2577
        nodeJet2N02704PlusPointP013Center2577) =
        nodeJet2N02704PlusPointP013Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP013RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP013Rounded2577‖ ≤
          nodeJet2N02704PlusPointP013Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP013Factor2577
      nodeJet2N02704PlusPointP013Center2577)
  rw [nodeJet2N02704PlusPointP013RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP013Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP013Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP013Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP013DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP013Factor2577,
      nodeJet2N02704PlusPointP013Error2577, rounding2542,
      nodeJet2N02704PlusPointP013Radius2577]

theorem nodeJet2N02704PlusPointP013DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP013Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP013RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP013Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP013Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP013Rounded2577]

def nodeJet2N02704PlusPointP014Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP014Radius2577 : ℝ := ((1099514623431 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704PlusPointP014RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP014Factor2577
        nodeJet2N02704PlusPointP014Center2577) =
        nodeJet2N02704PlusPointP014Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP014RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP014Rounded2577‖ ≤
          nodeJet2N02704PlusPointP014Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP014Factor2577
      nodeJet2N02704PlusPointP014Center2577)
  rw [nodeJet2N02704PlusPointP014RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP014Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP014Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP014Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP014DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP014Factor2577,
      nodeJet2N02704PlusPointP014Error2577, rounding2542,
      nodeJet2N02704PlusPointP014Radius2577]

theorem nodeJet2N02704PlusPointP014DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP014Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP014RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP014Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP014Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP014Rounded2577]

def nodeJet2N02704PlusPointP015Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP015Radius2577 : ℝ := ((2199029246885 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704PlusPointP015RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP015Factor2577
        nodeJet2N02704PlusPointP015Center2577) =
        nodeJet2N02704PlusPointP015Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP015RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP015Rounded2577‖ ≤
          nodeJet2N02704PlusPointP015Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP015Factor2577
      nodeJet2N02704PlusPointP015Center2577)
  rw [nodeJet2N02704PlusPointP015RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP015Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP015Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP015Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP015DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP015Factor2577,
      nodeJet2N02704PlusPointP015Error2577, rounding2542,
      nodeJet2N02704PlusPointP015Radius2577]

theorem nodeJet2N02704PlusPointP015DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP015Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP015RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP015Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP015Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP015Rounded2577]

def nodeJet2N02704PlusPointP016Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP016Radius2577 : ℝ := ((2199029246901 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704PlusPointP016RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP016Factor2577
        nodeJet2N02704PlusPointP016Center2577) =
        nodeJet2N02704PlusPointP016Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP016RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP016Rounded2577‖ ≤
          nodeJet2N02704PlusPointP016Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP016Factor2577
      nodeJet2N02704PlusPointP016Center2577)
  rw [nodeJet2N02704PlusPointP016RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP016Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP016Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP016Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP016DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP016Factor2577,
      nodeJet2N02704PlusPointP016Error2577, rounding2542,
      nodeJet2N02704PlusPointP016Radius2577]

theorem nodeJet2N02704PlusPointP016DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP016Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP016RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP016Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP016Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP016Rounded2577]

def nodeJet2N02704PlusPointP017Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP017Radius2577 : ℝ := ((2199029246933 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704PlusPointP017RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP017Factor2577
        nodeJet2N02704PlusPointP017Center2577) =
        nodeJet2N02704PlusPointP017Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP017RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP017Rounded2577‖ ≤
          nodeJet2N02704PlusPointP017Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP017Factor2577
      nodeJet2N02704PlusPointP017Center2577)
  rw [nodeJet2N02704PlusPointP017RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP017Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP017Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP017Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP017DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP017Factor2577,
      nodeJet2N02704PlusPointP017Error2577, rounding2542,
      nodeJet2N02704PlusPointP017Radius2577]

theorem nodeJet2N02704PlusPointP017DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP017Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP017RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP017Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP017Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP017Rounded2577]

def nodeJet2N02704PlusPointP018Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP018Radius2577 : ℝ := ((2199029246945 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704PlusPointP018RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP018Factor2577
        nodeJet2N02704PlusPointP018Center2577) =
        nodeJet2N02704PlusPointP018Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP018RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP018Rounded2577‖ ≤
          nodeJet2N02704PlusPointP018Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP018Factor2577
      nodeJet2N02704PlusPointP018Center2577)
  rw [nodeJet2N02704PlusPointP018RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP018Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP018Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP018Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP018DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP018Factor2577,
      nodeJet2N02704PlusPointP018Error2577, rounding2542,
      nodeJet2N02704PlusPointP018Radius2577]

theorem nodeJet2N02704PlusPointP018DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP018Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP018RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP018Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP018Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP018Rounded2577]

def nodeJet2N02704PlusPointP019Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP019Radius2577 : ℝ := ((1099514623483 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704PlusPointP019RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP019Factor2577
        nodeJet2N02704PlusPointP019Center2577) =
        nodeJet2N02704PlusPointP019Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP019RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP019Rounded2577‖ ≤
          nodeJet2N02704PlusPointP019Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP019Factor2577
      nodeJet2N02704PlusPointP019Center2577)
  rw [nodeJet2N02704PlusPointP019RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP019Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP019Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP019Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP019DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP019Factor2577,
      nodeJet2N02704PlusPointP019Error2577, rounding2542,
      nodeJet2N02704PlusPointP019Radius2577]

theorem nodeJet2N02704PlusPointP019DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP019Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP019RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP019Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP019Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP019Rounded2577]

def nodeJet2N02704PlusPointP020Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP020Radius2577 : ℝ := ((1099514623495 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704PlusPointP020RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP020Factor2577
        nodeJet2N02704PlusPointP020Center2577) =
        nodeJet2N02704PlusPointP020Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP020RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP020Rounded2577‖ ≤
          nodeJet2N02704PlusPointP020Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP020Factor2577
      nodeJet2N02704PlusPointP020Center2577)
  rw [nodeJet2N02704PlusPointP020RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP020Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP020Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP020Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP020DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP020Factor2577,
      nodeJet2N02704PlusPointP020Error2577, rounding2542,
      nodeJet2N02704PlusPointP020Radius2577]

theorem nodeJet2N02704PlusPointP020DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP020Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP020RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP020Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP020Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP020Rounded2577]

def nodeJet2N02704PlusPointP021Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP021Radius2577 : ℝ := ((1099514623505 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704PlusPointP021RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP021Factor2577
        nodeJet2N02704PlusPointP021Center2577) =
        nodeJet2N02704PlusPointP021Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP021RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP021Rounded2577‖ ≤
          nodeJet2N02704PlusPointP021Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP021Factor2577
      nodeJet2N02704PlusPointP021Center2577)
  rw [nodeJet2N02704PlusPointP021RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP021Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP021Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP021Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP021DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP021Factor2577,
      nodeJet2N02704PlusPointP021Error2577, rounding2542,
      nodeJet2N02704PlusPointP021Radius2577]

theorem nodeJet2N02704PlusPointP021DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP021Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP021RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP021Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP021Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP021Rounded2577]

def nodeJet2N02704PlusPointP022Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP022Radius2577 : ℝ := ((549757311755 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02704PlusPointP022RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP022Factor2577
        nodeJet2N02704PlusPointP022Center2577) =
        nodeJet2N02704PlusPointP022Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP022RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP022Rounded2577‖ ≤
          nodeJet2N02704PlusPointP022Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP022Factor2577
      nodeJet2N02704PlusPointP022Center2577)
  rw [nodeJet2N02704PlusPointP022RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP022Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP022Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP022Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP022DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP022Factor2577,
      nodeJet2N02704PlusPointP022Error2577, rounding2542,
      nodeJet2N02704PlusPointP022Radius2577]

theorem nodeJet2N02704PlusPointP022DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP022Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP022RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP022Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP022Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP022Rounded2577]

def nodeJet2N02704PlusPointP023Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP023Radius2577 : ℝ := ((2199029247049 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704PlusPointP023RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP023Factor2577
        nodeJet2N02704PlusPointP023Center2577) =
        nodeJet2N02704PlusPointP023Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP023RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP023Rounded2577‖ ≤
          nodeJet2N02704PlusPointP023Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP023Factor2577
      nodeJet2N02704PlusPointP023Center2577)
  rw [nodeJet2N02704PlusPointP023RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP023Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP023Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP023Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP023DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP023Factor2577,
      nodeJet2N02704PlusPointP023Error2577, rounding2542,
      nodeJet2N02704PlusPointP023Radius2577]

theorem nodeJet2N02704PlusPointP023DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP023Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP023RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP023Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP023Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP023Rounded2577]

def nodeJet2N02704PlusPointP024Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP024Radius2577 : ℝ := ((1099514623531 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704PlusPointP024RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP024Factor2577
        nodeJet2N02704PlusPointP024Center2577) =
        nodeJet2N02704PlusPointP024Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP024RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP024Rounded2577‖ ≤
          nodeJet2N02704PlusPointP024Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP024Factor2577
      nodeJet2N02704PlusPointP024Center2577)
  rw [nodeJet2N02704PlusPointP024RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP024Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP024Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP024Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP024DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP024Factor2577,
      nodeJet2N02704PlusPointP024Error2577, rounding2542,
      nodeJet2N02704PlusPointP024Radius2577]

theorem nodeJet2N02704PlusPointP024DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP024Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP024RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP024Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP024Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP024Rounded2577]

def nodeJet2N02704PlusPointP025Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP025Radius2577 : ℝ := ((2199029247079 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704PlusPointP025RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP025Factor2577
        nodeJet2N02704PlusPointP025Center2577) =
        nodeJet2N02704PlusPointP025Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP025RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP025Rounded2577‖ ≤
          nodeJet2N02704PlusPointP025Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP025Factor2577
      nodeJet2N02704PlusPointP025Center2577)
  rw [nodeJet2N02704PlusPointP025RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP025Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP025Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP025Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP025DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP025Factor2577,
      nodeJet2N02704PlusPointP025Error2577, rounding2542,
      nodeJet2N02704PlusPointP025Radius2577]

theorem nodeJet2N02704PlusPointP025DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP025Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP025RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP025Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP025Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP025Rounded2577]

def nodeJet2N02704PlusPointP026Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP026Radius2577 : ℝ := ((274878655887 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem nodeJet2N02704PlusPointP026RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP026Factor2577
        nodeJet2N02704PlusPointP026Center2577) =
        nodeJet2N02704PlusPointP026Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP026RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP026Rounded2577‖ ≤
          nodeJet2N02704PlusPointP026Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP026Factor2577
      nodeJet2N02704PlusPointP026Center2577)
  rw [nodeJet2N02704PlusPointP026RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP026Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP026Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP026Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP026DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP026Factor2577,
      nodeJet2N02704PlusPointP026Error2577, rounding2542,
      nodeJet2N02704PlusPointP026Radius2577]

theorem nodeJet2N02704PlusPointP026DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP026Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP026RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP026Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP026Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP026Rounded2577]

def nodeJet2N02704PlusPointP027Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP027Radius2577 : ℝ := ((137439327945 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem nodeJet2N02704PlusPointP027RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP027Factor2577
        nodeJet2N02704PlusPointP027Center2577) =
        nodeJet2N02704PlusPointP027Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP027RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP027Rounded2577‖ ≤
          nodeJet2N02704PlusPointP027Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP027Factor2577
      nodeJet2N02704PlusPointP027Center2577)
  rw [nodeJet2N02704PlusPointP027RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP027Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP027Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP027Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP027DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP027Factor2577,
      nodeJet2N02704PlusPointP027Error2577, rounding2542,
      nodeJet2N02704PlusPointP027Radius2577]

theorem nodeJet2N02704PlusPointP027DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP027Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP027RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP027Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP027Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP027Rounded2577]

def nodeJet2N02704PlusPointP028Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP028Radius2577 : ℝ := ((1099514623565 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02704PlusPointP028RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP028Factor2577
        nodeJet2N02704PlusPointP028Center2577) =
        nodeJet2N02704PlusPointP028Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP028RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP028Rounded2577‖ ≤
          nodeJet2N02704PlusPointP028Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP028Factor2577
      nodeJet2N02704PlusPointP028Center2577)
  rw [nodeJet2N02704PlusPointP028RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP028Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP028Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP028Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP028DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP028Factor2577,
      nodeJet2N02704PlusPointP028Error2577, rounding2542,
      nodeJet2N02704PlusPointP028Radius2577]

theorem nodeJet2N02704PlusPointP028DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP028Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP028RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP028Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP028Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP028Rounded2577]

def nodeJet2N02704PlusPointP029Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02704PlusPointP029Radius2577 : ℝ := ((2199029247145 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02704PlusPointP029RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02704PlusPointP029Factor2577
        nodeJet2N02704PlusPointP029Center2577) =
        nodeJet2N02704PlusPointP029Rounded2577 := by
  cbv

theorem nodeJet2N02704PlusPointP029RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02704PlusPointPosition2577 -
      embedPair2542 nodeJet2N02704PlusPointP029Rounded2577‖ ≤
          nodeJet2N02704PlusPointP029Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02704PlusPointP029Factor2577
      nodeJet2N02704PlusPointP029Center2577)
  rw [nodeJet2N02704PlusPointP029RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP029Factor2577 * embedPair2542
        nodeJet2N02704PlusPointP029Center2577)
    (embedPair2542 nodeJet2N02704PlusPointP029Rounded2577)).trans (add_le_add
        nodeJet2N02704PlusPointP029DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02704PlusPointP029Factor2577,
      nodeJet2N02704PlusPointP029Error2577, rounding2542,
      nodeJet2N02704PlusPointP029Radius2577]

theorem nodeJet2N02704PlusPointP029DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02704PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02704PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02704PlusPointPosition2577)
    (embedPair2542 nodeJet2N02704PlusPointP029Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02704PlusPointP029RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02704PlusPointP029Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02704PlusPointP029Radius2577, pairMagnitude2542,
      nodeJet2N02704PlusPointP029Rounded2577]

noncomputable def nodeJet2N02704PlusSignedValue2577 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 nodeJet2N02704PlusPointP000Rounded2577
  | 1 => embedPair2542 nodeJet2N02704PlusPointP001Rounded2577
  | 2 => embedPair2542 nodeJet2N02704PlusPointP002Rounded2577
  | 3 => embedPair2542 nodeJet2N02704PlusPointP003Rounded2577
  | 4 => embedPair2542 nodeJet2N02704PlusPointP004Rounded2577
  | 5 => embedPair2542 nodeJet2N02704PlusPointP005Rounded2577
  | 6 => embedPair2542 nodeJet2N02704PlusPointP006Rounded2577
  | 7 => embedPair2542 nodeJet2N02704PlusPointP007Rounded2577
  | 8 => embedPair2542 nodeJet2N02704PlusPointP008Rounded2577
  | 9 => embedPair2542 nodeJet2N02704PlusPointP009Rounded2577
  | 10 => embedPair2542 nodeJet2N02704PlusPointP010Rounded2577
  | 11 => embedPair2542 nodeJet2N02704PlusPointP011Rounded2577
  | 12 => embedPair2542 nodeJet2N02704PlusPointP012Rounded2577
  | 13 => embedPair2542 nodeJet2N02704PlusPointP013Rounded2577
  | 14 => embedPair2542 nodeJet2N02704PlusPointP014Rounded2577
  | 15 => embedPair2542 nodeJet2N02704PlusPointP015Rounded2577
  | 16 => embedPair2542 nodeJet2N02704PlusPointP016Rounded2577
  | 17 => embedPair2542 nodeJet2N02704PlusPointP017Rounded2577
  | 18 => embedPair2542 nodeJet2N02704PlusPointP018Rounded2577
  | 19 => embedPair2542 nodeJet2N02704PlusPointP019Rounded2577
  | 20 => embedPair2542 nodeJet2N02704PlusPointP020Rounded2577
  | 21 => embedPair2542 nodeJet2N02704PlusPointP021Rounded2577
  | 22 => embedPair2542 nodeJet2N02704PlusPointP022Rounded2577
  | 23 => embedPair2542 nodeJet2N02704PlusPointP023Rounded2577
  | 24 => embedPair2542 nodeJet2N02704PlusPointP024Rounded2577
  | 25 => embedPair2542 nodeJet2N02704PlusPointP025Rounded2577
  | 26 => embedPair2542 nodeJet2N02704PlusPointP026Rounded2577
  | 27 => embedPair2542 nodeJet2N02704PlusPointP027Rounded2577
  | 28 => embedPair2542 nodeJet2N02704PlusPointP028Rounded2577
  | 29 => embedPair2542 nodeJet2N02704PlusPointP029Rounded2577
  | _ => 0

noncomputable def nodeJet2N02704PlusSignedError2577 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => nodeJet2N02704PlusPointP000Radius2577
  | 1 => nodeJet2N02704PlusPointP001Radius2577
  | 2 => nodeJet2N02704PlusPointP002Radius2577
  | 3 => nodeJet2N02704PlusPointP003Radius2577
  | 4 => nodeJet2N02704PlusPointP004Radius2577
  | 5 => nodeJet2N02704PlusPointP005Radius2577
  | 6 => nodeJet2N02704PlusPointP006Radius2577
  | 7 => nodeJet2N02704PlusPointP007Radius2577
  | 8 => nodeJet2N02704PlusPointP008Radius2577
  | 9 => nodeJet2N02704PlusPointP009Radius2577
  | 10 => nodeJet2N02704PlusPointP010Radius2577
  | 11 => nodeJet2N02704PlusPointP011Radius2577
  | 12 => nodeJet2N02704PlusPointP012Radius2577
  | 13 => nodeJet2N02704PlusPointP013Radius2577
  | 14 => nodeJet2N02704PlusPointP014Radius2577
  | 15 => nodeJet2N02704PlusPointP015Radius2577
  | 16 => nodeJet2N02704PlusPointP016Radius2577
  | 17 => nodeJet2N02704PlusPointP017Radius2577
  | 18 => nodeJet2N02704PlusPointP018Radius2577
  | 19 => nodeJet2N02704PlusPointP019Radius2577
  | 20 => nodeJet2N02704PlusPointP020Radius2577
  | 21 => nodeJet2N02704PlusPointP021Radius2577
  | 22 => nodeJet2N02704PlusPointP022Radius2577
  | 23 => nodeJet2N02704PlusPointP023Radius2577
  | 24 => nodeJet2N02704PlusPointP024Radius2577
  | 25 => nodeJet2N02704PlusPointP025Radius2577
  | 26 => nodeJet2N02704PlusPointP026Radius2577
  | 27 => nodeJet2N02704PlusPointP027Radius2577
  | 28 => nodeJet2N02704PlusPointP028Radius2577
  | 29 => nodeJet2N02704PlusPointP029Radius2577
  | _ => 0

theorem nodeJet2N02704PlusSignedExpError2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02704PlusPointPosition2577 -
        nodeJet2N02704PlusSignedValue2577 i‖ ≤ nodeJet2N02704PlusSignedError2577 i := by
  fin_cases i
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP000RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP001RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP002RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP003RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP004RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP005RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP006RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP007RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP008RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP009RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP010RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP011RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP012RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP013RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP014RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP015RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP016RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP017RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP018RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP019RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP020RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP021RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP022RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP023RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP024RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP025RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP026RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP027RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP028RoundedError2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP029RoundedError2577

theorem nodeJet2N02704PlusSignedUnitNorm2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02704PlusPointPosition2577‖ ≤ 1 :=
        by
  fin_cases i
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP000DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP001DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP002DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP003DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP004DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP005DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP006DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP007DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP008DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP009DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP010DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP011DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP012DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP013DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP014DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP015DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP016DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP017DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP018DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP019DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP020DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP021DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP022DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP023DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP024DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP025DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP026DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP027DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP028DerivativeNorm2577
  · simpa only [nodeJet2N02704PlusSignedValue2577, nodeJet2N02704PlusSignedError2577] using
      nodeJet2N02704PlusPointP029DerivativeNorm2577

noncomputable def nodeJet2N02704PlusSignedSum2577 : ℂ := ⟨(((-(((727790202712 * 10^40
        + 7299678716599663612772741650657174305182) * 10^40
        + 6751924348957251976754441929460681091771) * 10^40
        + 9346169224189949295428058022705597576369)) : ℝ) /
        (((709803441694 * 10^40
        + 9286040520740311406294280797278912962090) * 10^40
        + 4324364277263734305479824015949823344796) * 10^40
        + 2659731992932150006119314388217384402944)),
    (((((376337252308 * 10^40
        + 2454346063962664468052629394183078972749) * 10^40
        + 8010498566151265227733116198778023682648) * 10^40
        + 8641449963165447204431148957333134260839) : ℝ) /
        (((709803441694 * 10^40
        + 9286040520740311406294280797278912962090) * 10^40
        + 4324364277263734305479824015949823344796) * 10^40
        + 2659731992932150006119314388217384402944))⟩

noncomputable def nodeJet2N02704PlusSignedUpper2577 : ℝ := ((115431131 : ℝ) /
        100000000)

theorem nodeJet2N02704PlusSignedSum_eq2577 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02704PlusSignedValue2577 i) =
      nodeJet2N02704PlusSignedSum2577 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        nodeJet2N02704PlusSignedValue2577,
      nodeJet2N02704PlusSignedSum2577, embedPair2542, nodeJet2N02704PlusPointP000Rounded2577,
      nodeJet2N02704PlusPointP001Rounded2577,
      nodeJet2N02704PlusPointP002Rounded2577,
      nodeJet2N02704PlusPointP003Rounded2577,
      nodeJet2N02704PlusPointP004Rounded2577,
      nodeJet2N02704PlusPointP005Rounded2577,
      nodeJet2N02704PlusPointP006Rounded2577,
      nodeJet2N02704PlusPointP007Rounded2577,
      nodeJet2N02704PlusPointP008Rounded2577,
      nodeJet2N02704PlusPointP009Rounded2577,
      nodeJet2N02704PlusPointP010Rounded2577,
      nodeJet2N02704PlusPointP011Rounded2577,
      nodeJet2N02704PlusPointP012Rounded2577,
      nodeJet2N02704PlusPointP013Rounded2577,
      nodeJet2N02704PlusPointP014Rounded2577,
      nodeJet2N02704PlusPointP015Rounded2577,
      nodeJet2N02704PlusPointP016Rounded2577,
      nodeJet2N02704PlusPointP017Rounded2577,
      nodeJet2N02704PlusPointP018Rounded2577,
      nodeJet2N02704PlusPointP019Rounded2577,
      nodeJet2N02704PlusPointP020Rounded2577,
      nodeJet2N02704PlusPointP021Rounded2577,
      nodeJet2N02704PlusPointP022Rounded2577,
      nodeJet2N02704PlusPointP023Rounded2577,
      nodeJet2N02704PlusPointP024Rounded2577,
      nodeJet2N02704PlusPointP025Rounded2577,
      nodeJet2N02704PlusPointP026Rounded2577,
      nodeJet2N02704PlusPointP027Rounded2577,
      nodeJet2N02704PlusPointP028Rounded2577,
      nodeJet2N02704PlusPointP029Rounded2577, Complex.mul_re, Complex.mul_im]

theorem nodeJet2N02704PlusSignedSum_norm2577 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02704PlusSignedValue2577 i‖ ≤
        ((115431121 :
        ℝ) /
        100000000) := by
  rw [nodeJet2N02704PlusSignedSum_eq2577]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [nodeJet2N02704PlusSignedSum2577]

theorem nodeJet2N02704PlusSignedCharge2577 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02704PlusSignedError2577 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      nodeJet2N02704PlusSignedError2577, nodeJet2N02704PlusPointP000Radius2577,
      nodeJet2N02704PlusPointP001Radius2577,
      nodeJet2N02704PlusPointP002Radius2577,
      nodeJet2N02704PlusPointP003Radius2577,
      nodeJet2N02704PlusPointP004Radius2577,
      nodeJet2N02704PlusPointP005Radius2577,
      nodeJet2N02704PlusPointP006Radius2577,
      nodeJet2N02704PlusPointP007Radius2577,
      nodeJet2N02704PlusPointP008Radius2577,
      nodeJet2N02704PlusPointP009Radius2577,
      nodeJet2N02704PlusPointP010Radius2577,
      nodeJet2N02704PlusPointP011Radius2577,
      nodeJet2N02704PlusPointP012Radius2577,
      nodeJet2N02704PlusPointP013Radius2577,
      nodeJet2N02704PlusPointP014Radius2577,
      nodeJet2N02704PlusPointP015Radius2577,
      nodeJet2N02704PlusPointP016Radius2577,
      nodeJet2N02704PlusPointP017Radius2577,
      nodeJet2N02704PlusPointP018Radius2577,
      nodeJet2N02704PlusPointP019Radius2577,
      nodeJet2N02704PlusPointP020Radius2577,
      nodeJet2N02704PlusPointP021Radius2577,
      nodeJet2N02704PlusPointP022Radius2577,
      nodeJet2N02704PlusPointP023Radius2577,
      nodeJet2N02704PlusPointP024Radius2577,
      nodeJet2N02704PlusPointP025Radius2577,
      nodeJet2N02704PlusPointP026Radius2577,
      nodeJet2N02704PlusPointP027Radius2577,
      nodeJet2N02704PlusPointP028Radius2577,
      nodeJet2N02704PlusPointP029Radius2577]

theorem nodeJet2N02704PlusSignedUpper_le2577 :
    signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 nodeJet2N02704PlusPointPosition2577 ≤ nodeJet2N02704PlusSignedUpper2577
          := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02704PlusPointPosition2577‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02704PlusSignedValue2577 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02704PlusSignedError2577 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (nodeJet2N02704PlusSignedExpError2577
        i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02704PlusPointPosition2577‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (nodeJet2N02704PlusSignedUnitNorm2577 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02704PlusPointPosition2577‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 nodeJet2N02704PlusSignedUpper2577
  linarith [nodeJet2N02704PlusSignedSum_norm2577, nodeJet2N02704PlusSignedCharge2577]

theorem nodeJet2N02704PlusPhysical2577 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        nodeJet2N02704PlusPointPosition2577‖ ≤
      nodeJet2N02704PlusSignedUpper2577 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        nodeJet2N02704PlusPointPosition2577
  exact h.trans nodeJet2N02704PlusSignedUpper_le2577

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.nodeJet2N02704PlusSignedExpError2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02704PlusSignedSum_eq2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02704PlusSignedCharge2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02704PlusSignedUpper_le2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02704PlusPhysical2577
