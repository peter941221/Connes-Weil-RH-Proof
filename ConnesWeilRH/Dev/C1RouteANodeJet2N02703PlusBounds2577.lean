import ConnesWeilRH.Dev.C1RouteANodeJet2N02703Plus2577
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem nodeJet2N02703PlusPoint_triangle2577 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def nodeJet2N02703PlusPointP000Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP000Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02703PlusPointP000RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP000Factor2577
        nodeJet2N02703PlusPointP000Center2577) =
        nodeJet2N02703PlusPointP000Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP000RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP000Rounded2577‖ ≤
          nodeJet2N02703PlusPointP000Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP000Factor2577
      nodeJet2N02703PlusPointP000Center2577)
  rw [nodeJet2N02703PlusPointP000RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP000Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP000Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP000Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP000DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP000Factor2577,
      nodeJet2N02703PlusPointP000Error2577, rounding2542,
      nodeJet2N02703PlusPointP000Radius2577]

theorem nodeJet2N02703PlusPointP000DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP000Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP000RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP000Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP000Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP000Rounded2577]

def nodeJet2N02703PlusPointP001Rounded2577 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP001Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP001RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP001Factor2577
        nodeJet2N02703PlusPointP001Center2577) =
        nodeJet2N02703PlusPointP001Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP001RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP001Rounded2577‖ ≤
          nodeJet2N02703PlusPointP001Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP001Factor2577
      nodeJet2N02703PlusPointP001Center2577)
  rw [nodeJet2N02703PlusPointP001RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP001Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP001Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP001Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP001DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP001Factor2577,
      nodeJet2N02703PlusPointP001Error2577, rounding2542,
      nodeJet2N02703PlusPointP001Radius2577]

theorem nodeJet2N02703PlusPointP001DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP001Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP001RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP001Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP001Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP001Rounded2577]

def nodeJet2N02703PlusPointP002Rounded2577 : RatPair2542 :=
  (((833847 : ℚ) /
        633825300114114700748351602688),
    (((-985435) : ℚ) /
        1267650600228229401496703205376))

noncomputable def nodeJet2N02703PlusPointP002Radius2577 : ℝ := ((1099511631597 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02703PlusPointP002RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP002Factor2577
        nodeJet2N02703PlusPointP002Center2577) =
        nodeJet2N02703PlusPointP002Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP002RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP002Rounded2577‖ ≤
          nodeJet2N02703PlusPointP002Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP002Factor2577
      nodeJet2N02703PlusPointP002Center2577)
  rw [nodeJet2N02703PlusPointP002RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP002Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP002Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP002Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP002DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP002Factor2577,
      nodeJet2N02703PlusPointP002Error2577, rounding2542,
      nodeJet2N02703PlusPointP002Radius2577]

theorem nodeJet2N02703PlusPointP002DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP002Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP002RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP002Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP002Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP002Rounded2577]

def nodeJet2N02703PlusPointP003Rounded2577 : RatPair2542 :=
  (((3886910868437 : ℚ) /
        316912650057057350374175801344),
    ((3005255763553 : ℚ) /
        633825300114114700748351602688))

noncomputable def nodeJet2N02703PlusPointP003Radius2577 : ℝ := ((1141066495649 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02703PlusPointP003RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP003Factor2577
        nodeJet2N02703PlusPointP003Center2577) =
        nodeJet2N02703PlusPointP003Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP003RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP003Rounded2577‖ ≤
          nodeJet2N02703PlusPointP003Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP003Factor2577
      nodeJet2N02703PlusPointP003Center2577)
  rw [nodeJet2N02703PlusPointP003RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP003Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP003Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP003Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP003DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP003Factor2577,
      nodeJet2N02703PlusPointP003Error2577, rounding2542,
      nodeJet2N02703PlusPointP003Radius2577]

theorem nodeJet2N02703PlusPointP003DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP003Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP003RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP003Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP003Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP003Rounded2577]

def nodeJet2N02703PlusPointP004Rounded2577 : RatPair2542 :=
  (((1421914918672861 : ℚ) /
        316912650057057350374175801344),
    (((-599278023063463) : ℚ) /
        158456325028528675187087900672))

noncomputable def nodeJet2N02703PlusPointP004Radius2577 : ℝ := ((1112668076069 : ℝ) /
        (4 * 10^40
        + 3556142965880123323311949751266331066368))

theorem nodeJet2N02703PlusPointP004RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP004Factor2577
        nodeJet2N02703PlusPointP004Center2577) =
        nodeJet2N02703PlusPointP004Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP004RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP004Rounded2577‖ ≤
          nodeJet2N02703PlusPointP004Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP004Factor2577
      nodeJet2N02703PlusPointP004Center2577)
  rw [nodeJet2N02703PlusPointP004RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP004Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP004Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP004Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP004DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP004Factor2577,
      nodeJet2N02703PlusPointP004Error2577, rounding2542,
      nodeJet2N02703PlusPointP004Radius2577]

theorem nodeJet2N02703PlusPointP004DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP004Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP004RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP004Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP004Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP004Rounded2577]

def nodeJet2N02703PlusPointP005Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP005Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02703PlusPointP005RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP005Factor2577
        nodeJet2N02703PlusPointP005Center2577) =
        nodeJet2N02703PlusPointP005Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP005RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP005Rounded2577‖ ≤
          nodeJet2N02703PlusPointP005Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP005Factor2577
      nodeJet2N02703PlusPointP005Center2577)
  rw [nodeJet2N02703PlusPointP005RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP005Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP005Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP005Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP005DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP005Factor2577,
      nodeJet2N02703PlusPointP005Error2577, rounding2542,
      nodeJet2N02703PlusPointP005Radius2577]

theorem nodeJet2N02703PlusPointP005DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP005Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP005RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP005Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP005Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP005Rounded2577]

def nodeJet2N02703PlusPointP006Rounded2577 : RatPair2542 :=
  (((5 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP006Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP006RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP006Factor2577
        nodeJet2N02703PlusPointP006Center2577) =
        nodeJet2N02703PlusPointP006Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP006RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP006Rounded2577‖ ≤
          nodeJet2N02703PlusPointP006Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP006Factor2577
      nodeJet2N02703PlusPointP006Center2577)
  rw [nodeJet2N02703PlusPointP006RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP006Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP006Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP006Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP006DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP006Factor2577,
      nodeJet2N02703PlusPointP006Error2577, rounding2542,
      nodeJet2N02703PlusPointP006Radius2577]

theorem nodeJet2N02703PlusPointP006DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP006Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP006RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP006Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP006Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP006Rounded2577]

def nodeJet2N02703PlusPointP007Rounded2577 : RatPair2542 :=
  (((482720692341 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP007Radius2577 : ℝ := ((1099651787017 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02703PlusPointP007RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP007Factor2577
        nodeJet2N02703PlusPointP007Center2577) =
        nodeJet2N02703PlusPointP007Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP007RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP007Rounded2577‖ ≤
          nodeJet2N02703PlusPointP007Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP007Factor2577
      nodeJet2N02703PlusPointP007Center2577)
  rw [nodeJet2N02703PlusPointP007RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP007Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP007Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP007Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP007DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP007Factor2577,
      nodeJet2N02703PlusPointP007Error2577, rounding2542,
      nodeJet2N02703PlusPointP007Radius2577]

theorem nodeJet2N02703PlusPointP007DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP007Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP007RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP007Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP007Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP007Rounded2577]

def nodeJet2N02703PlusPointP008Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP008Radius2577 : ℝ := ((2199042191701 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP008RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP008Factor2577
        nodeJet2N02703PlusPointP008Center2577) =
        nodeJet2N02703PlusPointP008Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP008RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP008Rounded2577‖ ≤
          nodeJet2N02703PlusPointP008Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP008Factor2577
      nodeJet2N02703PlusPointP008Center2577)
  rw [nodeJet2N02703PlusPointP008RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP008Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP008Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP008Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP008DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP008Factor2577,
      nodeJet2N02703PlusPointP008Error2577, rounding2542,
      nodeJet2N02703PlusPointP008Radius2577]

theorem nodeJet2N02703PlusPointP008DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP008Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP008RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP008Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP008Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP008Rounded2577]

def nodeJet2N02703PlusPointP009Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP009Radius2577 : ℝ := ((2199042191783 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP009RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP009Factor2577
        nodeJet2N02703PlusPointP009Center2577) =
        nodeJet2N02703PlusPointP009Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP009RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP009Rounded2577‖ ≤
          nodeJet2N02703PlusPointP009Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP009Factor2577
      nodeJet2N02703PlusPointP009Center2577)
  rw [nodeJet2N02703PlusPointP009RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP009Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP009Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP009Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP009DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP009Factor2577,
      nodeJet2N02703PlusPointP009Error2577, rounding2542,
      nodeJet2N02703PlusPointP009Radius2577]

theorem nodeJet2N02703PlusPointP009DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP009Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP009RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP009Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP009Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP009Rounded2577]

def nodeJet2N02703PlusPointP010Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP010Radius2577 : ℝ := ((2199042191831 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP010RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP010Factor2577
        nodeJet2N02703PlusPointP010Center2577) =
        nodeJet2N02703PlusPointP010Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP010RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP010Rounded2577‖ ≤
          nodeJet2N02703PlusPointP010Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP010Factor2577
      nodeJet2N02703PlusPointP010Center2577)
  rw [nodeJet2N02703PlusPointP010RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP010Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP010Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP010Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP010DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP010Factor2577,
      nodeJet2N02703PlusPointP010Error2577, rounding2542,
      nodeJet2N02703PlusPointP010Radius2577]

theorem nodeJet2N02703PlusPointP010DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP010Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP010RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP010Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP010Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP010Rounded2577]

def nodeJet2N02703PlusPointP011Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP011Radius2577 : ℝ := ((2199042191863 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP011RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP011Factor2577
        nodeJet2N02703PlusPointP011Center2577) =
        nodeJet2N02703PlusPointP011Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP011RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP011Rounded2577‖ ≤
          nodeJet2N02703PlusPointP011Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP011Factor2577
      nodeJet2N02703PlusPointP011Center2577)
  rw [nodeJet2N02703PlusPointP011RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP011Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP011Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP011Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP011DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP011Factor2577,
      nodeJet2N02703PlusPointP011Error2577, rounding2542,
      nodeJet2N02703PlusPointP011Radius2577]

theorem nodeJet2N02703PlusPointP011DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP011Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP011RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP011Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP011Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP011Rounded2577]

def nodeJet2N02703PlusPointP012Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP012Radius2577 : ℝ := ((274880273987 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem nodeJet2N02703PlusPointP012RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP012Factor2577
        nodeJet2N02703PlusPointP012Center2577) =
        nodeJet2N02703PlusPointP012Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP012RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP012Rounded2577‖ ≤
          nodeJet2N02703PlusPointP012Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP012Factor2577
      nodeJet2N02703PlusPointP012Center2577)
  rw [nodeJet2N02703PlusPointP012RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP012Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP012Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP012Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP012DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP012Factor2577,
      nodeJet2N02703PlusPointP012Error2577, rounding2542,
      nodeJet2N02703PlusPointP012Radius2577]

theorem nodeJet2N02703PlusPointP012DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP012Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP012RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP012Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP012Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP012Rounded2577]

def nodeJet2N02703PlusPointP013Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP013Radius2577 : ℝ := ((2199042191927 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP013RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP013Factor2577
        nodeJet2N02703PlusPointP013Center2577) =
        nodeJet2N02703PlusPointP013Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP013RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP013Rounded2577‖ ≤
          nodeJet2N02703PlusPointP013Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP013Factor2577
      nodeJet2N02703PlusPointP013Center2577)
  rw [nodeJet2N02703PlusPointP013RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP013Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP013Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP013Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP013DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP013Factor2577,
      nodeJet2N02703PlusPointP013Error2577, rounding2542,
      nodeJet2N02703PlusPointP013Radius2577]

theorem nodeJet2N02703PlusPointP013DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP013Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP013RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP013Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP013Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP013Rounded2577]

def nodeJet2N02703PlusPointP014Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP014Radius2577 : ℝ := ((1099521095991 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02703PlusPointP014RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP014Factor2577
        nodeJet2N02703PlusPointP014Center2577) =
        nodeJet2N02703PlusPointP014Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP014RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP014Rounded2577‖ ≤
          nodeJet2N02703PlusPointP014Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP014Factor2577
      nodeJet2N02703PlusPointP014Center2577)
  rw [nodeJet2N02703PlusPointP014RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP014Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP014Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP014Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP014DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP014Factor2577,
      nodeJet2N02703PlusPointP014Error2577, rounding2542,
      nodeJet2N02703PlusPointP014Radius2577]

theorem nodeJet2N02703PlusPointP014DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP014Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP014RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP014Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP014Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP014Rounded2577]

def nodeJet2N02703PlusPointP015Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP015Radius2577 : ℝ := ((2199042192023 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP015RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP015Factor2577
        nodeJet2N02703PlusPointP015Center2577) =
        nodeJet2N02703PlusPointP015Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP015RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP015Rounded2577‖ ≤
          nodeJet2N02703PlusPointP015Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP015Factor2577
      nodeJet2N02703PlusPointP015Center2577)
  rw [nodeJet2N02703PlusPointP015RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP015Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP015Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP015Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP015DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP015Factor2577,
      nodeJet2N02703PlusPointP015Error2577, rounding2542,
      nodeJet2N02703PlusPointP015Radius2577]

theorem nodeJet2N02703PlusPointP015DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP015Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP015RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP015Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP015Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP015Rounded2577]

def nodeJet2N02703PlusPointP016Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP016Radius2577 : ℝ := ((549760548013 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02703PlusPointP016RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP016Factor2577
        nodeJet2N02703PlusPointP016Center2577) =
        nodeJet2N02703PlusPointP016Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP016RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP016Rounded2577‖ ≤
          nodeJet2N02703PlusPointP016Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP016Factor2577
      nodeJet2N02703PlusPointP016Center2577)
  rw [nodeJet2N02703PlusPointP016RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP016Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP016Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP016Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP016DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP016Factor2577,
      nodeJet2N02703PlusPointP016Error2577, rounding2542,
      nodeJet2N02703PlusPointP016Radius2577]

theorem nodeJet2N02703PlusPointP016DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP016Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP016RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP016Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP016Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP016Rounded2577]

def nodeJet2N02703PlusPointP017Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP017Radius2577 : ℝ := ((549760548027 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02703PlusPointP017RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP017Factor2577
        nodeJet2N02703PlusPointP017Center2577) =
        nodeJet2N02703PlusPointP017Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP017RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP017Rounded2577‖ ≤
          nodeJet2N02703PlusPointP017Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP017Factor2577
      nodeJet2N02703PlusPointP017Center2577)
  rw [nodeJet2N02703PlusPointP017RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP017Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP017Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP017Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP017DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP017Factor2577,
      nodeJet2N02703PlusPointP017Error2577, rounding2542,
      nodeJet2N02703PlusPointP017Radius2577]

theorem nodeJet2N02703PlusPointP017DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP017Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP017RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP017Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP017Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP017Rounded2577]

def nodeJet2N02703PlusPointP018Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP018Radius2577 : ℝ := ((2199042192129 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP018RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP018Factor2577
        nodeJet2N02703PlusPointP018Center2577) =
        nodeJet2N02703PlusPointP018Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP018RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP018Rounded2577‖ ≤
          nodeJet2N02703PlusPointP018Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP018Factor2577
      nodeJet2N02703PlusPointP018Center2577)
  rw [nodeJet2N02703PlusPointP018RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP018Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP018Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP018Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP018DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP018Factor2577,
      nodeJet2N02703PlusPointP018Error2577, rounding2542,
      nodeJet2N02703PlusPointP018Radius2577]

theorem nodeJet2N02703PlusPointP018DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP018Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP018RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP018Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP018Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP018Rounded2577]

def nodeJet2N02703PlusPointP019Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP019Radius2577 : ℝ := ((2199042192167 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP019RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP019Factor2577
        nodeJet2N02703PlusPointP019Center2577) =
        nodeJet2N02703PlusPointP019Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP019RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP019Rounded2577‖ ≤
          nodeJet2N02703PlusPointP019Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP019Factor2577
      nodeJet2N02703PlusPointP019Center2577)
  rw [nodeJet2N02703PlusPointP019RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP019Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP019Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP019Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP019DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP019Factor2577,
      nodeJet2N02703PlusPointP019Error2577, rounding2542,
      nodeJet2N02703PlusPointP019Radius2577]

theorem nodeJet2N02703PlusPointP019DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP019Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP019RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP019Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP019Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP019Rounded2577]

def nodeJet2N02703PlusPointP020Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP020Radius2577 : ℝ := ((2199042192209 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP020RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP020Factor2577
        nodeJet2N02703PlusPointP020Center2577) =
        nodeJet2N02703PlusPointP020Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP020RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP020Rounded2577‖ ≤
          nodeJet2N02703PlusPointP020Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP020Factor2577
      nodeJet2N02703PlusPointP020Center2577)
  rw [nodeJet2N02703PlusPointP020RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP020Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP020Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP020Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP020DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP020Factor2577,
      nodeJet2N02703PlusPointP020Error2577, rounding2542,
      nodeJet2N02703PlusPointP020Radius2577]

theorem nodeJet2N02703PlusPointP020DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP020Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP020RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP020Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP020Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP020Rounded2577]

def nodeJet2N02703PlusPointP021Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP021Radius2577 : ℝ := ((549760548061 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02703PlusPointP021RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP021Factor2577
        nodeJet2N02703PlusPointP021Center2577) =
        nodeJet2N02703PlusPointP021Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP021RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP021Rounded2577‖ ≤
          nodeJet2N02703PlusPointP021Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP021Factor2577
      nodeJet2N02703PlusPointP021Center2577)
  rw [nodeJet2N02703PlusPointP021RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP021Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP021Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP021Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP021DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP021Factor2577,
      nodeJet2N02703PlusPointP021Error2577, rounding2542,
      nodeJet2N02703PlusPointP021Radius2577]

theorem nodeJet2N02703PlusPointP021DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP021Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP021RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP021Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP021Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP021Rounded2577]

def nodeJet2N02703PlusPointP022Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP022Radius2577 : ℝ := ((1099521096131 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02703PlusPointP022RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP022Factor2577
        nodeJet2N02703PlusPointP022Center2577) =
        nodeJet2N02703PlusPointP022Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP022RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP022Rounded2577‖ ≤
          nodeJet2N02703PlusPointP022Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP022Factor2577
      nodeJet2N02703PlusPointP022Center2577)
  rw [nodeJet2N02703PlusPointP022RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP022Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP022Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP022Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP022DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP022Factor2577,
      nodeJet2N02703PlusPointP022Error2577, rounding2542,
      nodeJet2N02703PlusPointP022Radius2577]

theorem nodeJet2N02703PlusPointP022DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP022Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP022RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP022Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP022Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP022Rounded2577]

def nodeJet2N02703PlusPointP023Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP023Radius2577 : ℝ := ((2199042192313 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP023RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP023Factor2577
        nodeJet2N02703PlusPointP023Center2577) =
        nodeJet2N02703PlusPointP023Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP023RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP023Rounded2577‖ ≤
          nodeJet2N02703PlusPointP023Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP023Factor2577
      nodeJet2N02703PlusPointP023Center2577)
  rw [nodeJet2N02703PlusPointP023RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP023Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP023Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP023Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP023DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP023Factor2577,
      nodeJet2N02703PlusPointP023Error2577, rounding2542,
      nodeJet2N02703PlusPointP023Radius2577]

theorem nodeJet2N02703PlusPointP023DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP023Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP023RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP023Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP023Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP023Rounded2577]

def nodeJet2N02703PlusPointP024Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP024Radius2577 : ℝ := ((2199042192337 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP024RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP024Factor2577
        nodeJet2N02703PlusPointP024Center2577) =
        nodeJet2N02703PlusPointP024Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP024RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP024Rounded2577‖ ≤
          nodeJet2N02703PlusPointP024Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP024Factor2577
      nodeJet2N02703PlusPointP024Center2577)
  rw [nodeJet2N02703PlusPointP024RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP024Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP024Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP024Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP024DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP024Factor2577,
      nodeJet2N02703PlusPointP024Error2577, rounding2542,
      nodeJet2N02703PlusPointP024Radius2577]

theorem nodeJet2N02703PlusPointP024DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP024Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP024RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP024Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP024Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP024Rounded2577]

def nodeJet2N02703PlusPointP025Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP025Radius2577 : ℝ := ((2199042192367 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP025RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP025Factor2577
        nodeJet2N02703PlusPointP025Center2577) =
        nodeJet2N02703PlusPointP025Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP025RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP025Rounded2577‖ ≤
          nodeJet2N02703PlusPointP025Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP025Factor2577
      nodeJet2N02703PlusPointP025Center2577)
  rw [nodeJet2N02703PlusPointP025RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP025Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP025Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP025Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP025DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP025Factor2577,
      nodeJet2N02703PlusPointP025Error2577, rounding2542,
      nodeJet2N02703PlusPointP025Radius2577]

theorem nodeJet2N02703PlusPointP025DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP025Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP025RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP025Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP025Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP025Rounded2577]

def nodeJet2N02703PlusPointP026Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP026Radius2577 : ℝ := ((2199042192397 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP026RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP026Factor2577
        nodeJet2N02703PlusPointP026Center2577) =
        nodeJet2N02703PlusPointP026Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP026RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP026Rounded2577‖ ≤
          nodeJet2N02703PlusPointP026Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP026Factor2577
      nodeJet2N02703PlusPointP026Center2577)
  rw [nodeJet2N02703PlusPointP026RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP026Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP026Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP026Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP026DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP026Factor2577,
      nodeJet2N02703PlusPointP026Error2577, rounding2542,
      nodeJet2N02703PlusPointP026Radius2577]

theorem nodeJet2N02703PlusPointP026DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP026Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP026RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP026Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP026Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP026Rounded2577]

def nodeJet2N02703PlusPointP027Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP027Radius2577 : ℝ := ((2199042192441 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02703PlusPointP027RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP027Factor2577
        nodeJet2N02703PlusPointP027Center2577) =
        nodeJet2N02703PlusPointP027Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP027RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP027Rounded2577‖ ≤
          nodeJet2N02703PlusPointP027Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP027Factor2577
      nodeJet2N02703PlusPointP027Center2577)
  rw [nodeJet2N02703PlusPointP027RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP027Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP027Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP027Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP027DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP027Factor2577,
      nodeJet2N02703PlusPointP027Error2577, rounding2542,
      nodeJet2N02703PlusPointP027Radius2577]

theorem nodeJet2N02703PlusPointP027DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP027Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP027RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP027Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP027Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP027Rounded2577]

def nodeJet2N02703PlusPointP028Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP028Radius2577 : ℝ := ((1099521096229 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02703PlusPointP028RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP028Factor2577
        nodeJet2N02703PlusPointP028Center2577) =
        nodeJet2N02703PlusPointP028Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP028RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP028Rounded2577‖ ≤
          nodeJet2N02703PlusPointP028Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP028Factor2577
      nodeJet2N02703PlusPointP028Center2577)
  rw [nodeJet2N02703PlusPointP028RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP028Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP028Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP028Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP028DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP028Factor2577,
      nodeJet2N02703PlusPointP028Error2577, rounding2542,
      nodeJet2N02703PlusPointP028Radius2577]

theorem nodeJet2N02703PlusPointP028DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP028Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP028RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP028Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP028Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP028Rounded2577]

def nodeJet2N02703PlusPointP029Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02703PlusPointP029Radius2577 : ℝ := ((549760548121 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02703PlusPointP029RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02703PlusPointP029Factor2577
        nodeJet2N02703PlusPointP029Center2577) =
        nodeJet2N02703PlusPointP029Rounded2577 := by
  cbv

theorem nodeJet2N02703PlusPointP029RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02703PlusPointPosition2577 -
      embedPair2542 nodeJet2N02703PlusPointP029Rounded2577‖ ≤
          nodeJet2N02703PlusPointP029Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02703PlusPointP029Factor2577
      nodeJet2N02703PlusPointP029Center2577)
  rw [nodeJet2N02703PlusPointP029RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP029Factor2577 * embedPair2542
        nodeJet2N02703PlusPointP029Center2577)
    (embedPair2542 nodeJet2N02703PlusPointP029Rounded2577)).trans (add_le_add
        nodeJet2N02703PlusPointP029DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02703PlusPointP029Factor2577,
      nodeJet2N02703PlusPointP029Error2577, rounding2542,
      nodeJet2N02703PlusPointP029Radius2577]

theorem nodeJet2N02703PlusPointP029DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02703PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02703PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02703PlusPointPosition2577)
    (embedPair2542 nodeJet2N02703PlusPointP029Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02703PlusPointP029RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02703PlusPointP029Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02703PlusPointP029Radius2577, pairMagnitude2542,
      nodeJet2N02703PlusPointP029Rounded2577]

noncomputable def nodeJet2N02703PlusSignedValue2577 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 nodeJet2N02703PlusPointP000Rounded2577
  | 1 => embedPair2542 nodeJet2N02703PlusPointP001Rounded2577
  | 2 => embedPair2542 nodeJet2N02703PlusPointP002Rounded2577
  | 3 => embedPair2542 nodeJet2N02703PlusPointP003Rounded2577
  | 4 => embedPair2542 nodeJet2N02703PlusPointP004Rounded2577
  | 5 => embedPair2542 nodeJet2N02703PlusPointP005Rounded2577
  | 6 => embedPair2542 nodeJet2N02703PlusPointP006Rounded2577
  | 7 => embedPair2542 nodeJet2N02703PlusPointP007Rounded2577
  | 8 => embedPair2542 nodeJet2N02703PlusPointP008Rounded2577
  | 9 => embedPair2542 nodeJet2N02703PlusPointP009Rounded2577
  | 10 => embedPair2542 nodeJet2N02703PlusPointP010Rounded2577
  | 11 => embedPair2542 nodeJet2N02703PlusPointP011Rounded2577
  | 12 => embedPair2542 nodeJet2N02703PlusPointP012Rounded2577
  | 13 => embedPair2542 nodeJet2N02703PlusPointP013Rounded2577
  | 14 => embedPair2542 nodeJet2N02703PlusPointP014Rounded2577
  | 15 => embedPair2542 nodeJet2N02703PlusPointP015Rounded2577
  | 16 => embedPair2542 nodeJet2N02703PlusPointP016Rounded2577
  | 17 => embedPair2542 nodeJet2N02703PlusPointP017Rounded2577
  | 18 => embedPair2542 nodeJet2N02703PlusPointP018Rounded2577
  | 19 => embedPair2542 nodeJet2N02703PlusPointP019Rounded2577
  | 20 => embedPair2542 nodeJet2N02703PlusPointP020Rounded2577
  | 21 => embedPair2542 nodeJet2N02703PlusPointP021Rounded2577
  | 22 => embedPair2542 nodeJet2N02703PlusPointP022Rounded2577
  | 23 => embedPair2542 nodeJet2N02703PlusPointP023Rounded2577
  | 24 => embedPair2542 nodeJet2N02703PlusPointP024Rounded2577
  | 25 => embedPair2542 nodeJet2N02703PlusPointP025Rounded2577
  | 26 => embedPair2542 nodeJet2N02703PlusPointP026Rounded2577
  | 27 => embedPair2542 nodeJet2N02703PlusPointP027Rounded2577
  | 28 => embedPair2542 nodeJet2N02703PlusPointP028Rounded2577
  | 29 => embedPair2542 nodeJet2N02703PlusPointP029Rounded2577
  | _ => 0

noncomputable def nodeJet2N02703PlusSignedError2577 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => nodeJet2N02703PlusPointP000Radius2577
  | 1 => nodeJet2N02703PlusPointP001Radius2577
  | 2 => nodeJet2N02703PlusPointP002Radius2577
  | 3 => nodeJet2N02703PlusPointP003Radius2577
  | 4 => nodeJet2N02703PlusPointP004Radius2577
  | 5 => nodeJet2N02703PlusPointP005Radius2577
  | 6 => nodeJet2N02703PlusPointP006Radius2577
  | 7 => nodeJet2N02703PlusPointP007Radius2577
  | 8 => nodeJet2N02703PlusPointP008Radius2577
  | 9 => nodeJet2N02703PlusPointP009Radius2577
  | 10 => nodeJet2N02703PlusPointP010Radius2577
  | 11 => nodeJet2N02703PlusPointP011Radius2577
  | 12 => nodeJet2N02703PlusPointP012Radius2577
  | 13 => nodeJet2N02703PlusPointP013Radius2577
  | 14 => nodeJet2N02703PlusPointP014Radius2577
  | 15 => nodeJet2N02703PlusPointP015Radius2577
  | 16 => nodeJet2N02703PlusPointP016Radius2577
  | 17 => nodeJet2N02703PlusPointP017Radius2577
  | 18 => nodeJet2N02703PlusPointP018Radius2577
  | 19 => nodeJet2N02703PlusPointP019Radius2577
  | 20 => nodeJet2N02703PlusPointP020Radius2577
  | 21 => nodeJet2N02703PlusPointP021Radius2577
  | 22 => nodeJet2N02703PlusPointP022Radius2577
  | 23 => nodeJet2N02703PlusPointP023Radius2577
  | 24 => nodeJet2N02703PlusPointP024Radius2577
  | 25 => nodeJet2N02703PlusPointP025Radius2577
  | 26 => nodeJet2N02703PlusPointP026Radius2577
  | 27 => nodeJet2N02703PlusPointP027Radius2577
  | 28 => nodeJet2N02703PlusPointP028Radius2577
  | 29 => nodeJet2N02703PlusPointP029Radius2577
  | _ => 0

theorem nodeJet2N02703PlusSignedExpError2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02703PlusPointPosition2577 -
        nodeJet2N02703PlusSignedValue2577 i‖ ≤ nodeJet2N02703PlusSignedError2577 i := by
  fin_cases i
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP000RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP001RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP002RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP003RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP004RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP005RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP006RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP007RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP008RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP009RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP010RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP011RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP012RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP013RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP014RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP015RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP016RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP017RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP018RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP019RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP020RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP021RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP022RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP023RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP024RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP025RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP026RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP027RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP028RoundedError2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP029RoundedError2577

theorem nodeJet2N02703PlusSignedUnitNorm2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02703PlusPointPosition2577‖ ≤ 1 :=
        by
  fin_cases i
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP000DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP001DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP002DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP003DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP004DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP005DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP006DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP007DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP008DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP009DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP010DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP011DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP012DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP013DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP014DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP015DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP016DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP017DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP018DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP019DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP020DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP021DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP022DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP023DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP024DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP025DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP026DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP027DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP028DerivativeNorm2577
  · simpa only [nodeJet2N02703PlusSignedValue2577, nodeJet2N02703PlusSignedError2577] using
      nodeJet2N02703PlusPointP029DerivativeNorm2577

noncomputable def nodeJet2N02703PlusSignedSum2577 : ℂ := ⟨(((-(((1477306765979 * 10^40
        + 1446839274423348922332043024321827778734) * 10^40
        + 5076668419624900771317523005164113413476) * 10^40
        + 5711470355071920091889595738726858741541)) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888)),
    (((((335796157621 * 10^40
        + 9757774769209786988593415559248427819267) * 10^40
        + 7966123989982834472988684162431698639806) * 10^40
        + 3784678852764282510266181052257780630845) : ℝ) /
        (((709803441694 * 10^40
        + 9286040520740311406294280797278912962090) * 10^40
        + 4324364277263734305479824015949823344796) * 10^40
        + 2659731992932150006119314388217384402944))⟩

noncomputable def nodeJet2N02703PlusSignedUpper2577 : ℝ := ((114313167 : ℝ) /
        100000000)

theorem nodeJet2N02703PlusSignedSum_eq2577 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02703PlusSignedValue2577 i) =
      nodeJet2N02703PlusSignedSum2577 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        nodeJet2N02703PlusSignedValue2577,
      nodeJet2N02703PlusSignedSum2577, embedPair2542, nodeJet2N02703PlusPointP000Rounded2577,
      nodeJet2N02703PlusPointP001Rounded2577,
      nodeJet2N02703PlusPointP002Rounded2577,
      nodeJet2N02703PlusPointP003Rounded2577,
      nodeJet2N02703PlusPointP004Rounded2577,
      nodeJet2N02703PlusPointP005Rounded2577,
      nodeJet2N02703PlusPointP006Rounded2577,
      nodeJet2N02703PlusPointP007Rounded2577,
      nodeJet2N02703PlusPointP008Rounded2577,
      nodeJet2N02703PlusPointP009Rounded2577,
      nodeJet2N02703PlusPointP010Rounded2577,
      nodeJet2N02703PlusPointP011Rounded2577,
      nodeJet2N02703PlusPointP012Rounded2577,
      nodeJet2N02703PlusPointP013Rounded2577,
      nodeJet2N02703PlusPointP014Rounded2577,
      nodeJet2N02703PlusPointP015Rounded2577,
      nodeJet2N02703PlusPointP016Rounded2577,
      nodeJet2N02703PlusPointP017Rounded2577,
      nodeJet2N02703PlusPointP018Rounded2577,
      nodeJet2N02703PlusPointP019Rounded2577,
      nodeJet2N02703PlusPointP020Rounded2577,
      nodeJet2N02703PlusPointP021Rounded2577,
      nodeJet2N02703PlusPointP022Rounded2577,
      nodeJet2N02703PlusPointP023Rounded2577,
      nodeJet2N02703PlusPointP024Rounded2577,
      nodeJet2N02703PlusPointP025Rounded2577,
      nodeJet2N02703PlusPointP026Rounded2577,
      nodeJet2N02703PlusPointP027Rounded2577,
      nodeJet2N02703PlusPointP028Rounded2577,
      nodeJet2N02703PlusPointP029Rounded2577, Complex.mul_re, Complex.mul_im]

theorem nodeJet2N02703PlusSignedSum_norm2577 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02703PlusSignedValue2577 i‖ ≤
        ((114313157 :
        ℝ) /
        100000000) := by
  rw [nodeJet2N02703PlusSignedSum_eq2577]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [nodeJet2N02703PlusSignedSum2577]

theorem nodeJet2N02703PlusSignedCharge2577 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02703PlusSignedError2577 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      nodeJet2N02703PlusSignedError2577, nodeJet2N02703PlusPointP000Radius2577,
      nodeJet2N02703PlusPointP001Radius2577,
      nodeJet2N02703PlusPointP002Radius2577,
      nodeJet2N02703PlusPointP003Radius2577,
      nodeJet2N02703PlusPointP004Radius2577,
      nodeJet2N02703PlusPointP005Radius2577,
      nodeJet2N02703PlusPointP006Radius2577,
      nodeJet2N02703PlusPointP007Radius2577,
      nodeJet2N02703PlusPointP008Radius2577,
      nodeJet2N02703PlusPointP009Radius2577,
      nodeJet2N02703PlusPointP010Radius2577,
      nodeJet2N02703PlusPointP011Radius2577,
      nodeJet2N02703PlusPointP012Radius2577,
      nodeJet2N02703PlusPointP013Radius2577,
      nodeJet2N02703PlusPointP014Radius2577,
      nodeJet2N02703PlusPointP015Radius2577,
      nodeJet2N02703PlusPointP016Radius2577,
      nodeJet2N02703PlusPointP017Radius2577,
      nodeJet2N02703PlusPointP018Radius2577,
      nodeJet2N02703PlusPointP019Radius2577,
      nodeJet2N02703PlusPointP020Radius2577,
      nodeJet2N02703PlusPointP021Radius2577,
      nodeJet2N02703PlusPointP022Radius2577,
      nodeJet2N02703PlusPointP023Radius2577,
      nodeJet2N02703PlusPointP024Radius2577,
      nodeJet2N02703PlusPointP025Radius2577,
      nodeJet2N02703PlusPointP026Radius2577,
      nodeJet2N02703PlusPointP027Radius2577,
      nodeJet2N02703PlusPointP028Radius2577,
      nodeJet2N02703PlusPointP029Radius2577]

theorem nodeJet2N02703PlusSignedUpper_le2577 :
    signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 nodeJet2N02703PlusPointPosition2577 ≤ nodeJet2N02703PlusSignedUpper2577
          := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02703PlusPointPosition2577‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02703PlusSignedValue2577 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02703PlusSignedError2577 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (nodeJet2N02703PlusSignedExpError2577
        i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02703PlusPointPosition2577‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (nodeJet2N02703PlusSignedUnitNorm2577 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02703PlusPointPosition2577‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 nodeJet2N02703PlusSignedUpper2577
  linarith [nodeJet2N02703PlusSignedSum_norm2577, nodeJet2N02703PlusSignedCharge2577]

theorem nodeJet2N02703PlusPhysical2577 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        nodeJet2N02703PlusPointPosition2577‖ ≤
      nodeJet2N02703PlusSignedUpper2577 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        nodeJet2N02703PlusPointPosition2577
  exact h.trans nodeJet2N02703PlusSignedUpper_le2577

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.nodeJet2N02703PlusSignedExpError2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02703PlusSignedSum_eq2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02703PlusSignedCharge2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02703PlusSignedUpper_le2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02703PlusPhysical2577
