import ConnesWeilRH.Dev.C1RouteANodeJet2N02705Plus2577
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem nodeJet2N02705PlusPoint_triangle2577 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def nodeJet2N02705PlusPointP000Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP000Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02705PlusPointP000RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP000Factor2577
        nodeJet2N02705PlusPointP000Center2577) =
        nodeJet2N02705PlusPointP000Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP000RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP000Rounded2577‖ ≤
          nodeJet2N02705PlusPointP000Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP000Factor2577
      nodeJet2N02705PlusPointP000Center2577)
  rw [nodeJet2N02705PlusPointP000RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP000Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP000Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP000Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP000DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP000Factor2577,
      nodeJet2N02705PlusPointP000Error2577, rounding2542,
      nodeJet2N02705PlusPointP000Radius2577]

theorem nodeJet2N02705PlusPointP000DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP000Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP000RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP000Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP000Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP000Rounded2577]

def nodeJet2N02705PlusPointP001Rounded2577 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP001Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705PlusPointP001RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP001Factor2577
        nodeJet2N02705PlusPointP001Center2577) =
        nodeJet2N02705PlusPointP001Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP001RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP001Rounded2577‖ ≤
          nodeJet2N02705PlusPointP001Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP001Factor2577
      nodeJet2N02705PlusPointP001Center2577)
  rw [nodeJet2N02705PlusPointP001RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP001Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP001Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP001Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP001DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP001Factor2577,
      nodeJet2N02705PlusPointP001Error2577, rounding2542,
      nodeJet2N02705PlusPointP001Radius2577]

theorem nodeJet2N02705PlusPointP001DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP001Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP001RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP001Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP001Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP001Rounded2577]

def nodeJet2N02705PlusPointP002Rounded2577 : RatPair2542 :=
  (((488137 : ℚ) /
        316912650057057350374175801344),
    (((-893159) : ℚ) /
        1267650600228229401496703205376))

noncomputable def nodeJet2N02705PlusPointP002Radius2577 : ℝ := ((2199023264067 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705PlusPointP002RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP002Factor2577
        nodeJet2N02705PlusPointP002Center2577) =
        nodeJet2N02705PlusPointP002Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP002RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP002Rounded2577‖ ≤
          nodeJet2N02705PlusPointP002Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP002Factor2577
      nodeJet2N02705PlusPointP002Center2577)
  rw [nodeJet2N02705PlusPointP002RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP002Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP002Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP002Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP002DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP002Factor2577,
      nodeJet2N02705PlusPointP002Error2577, rounding2542,
      nodeJet2N02705PlusPointP002Radius2577]

theorem nodeJet2N02705PlusPointP002DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP002Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP002RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP002Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP002Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP002Rounded2577]

def nodeJet2N02705PlusPointP003Rounded2577 : RatPair2542 :=
  (((15417909456635 : ℚ) /
        1267650600228229401496703205376),
    ((7849627995159 : ℚ) /
        1267650600228229401496703205376))

noncomputable def nodeJet2N02705PlusPointP003Radius2577 : ℝ := ((142879884253 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem nodeJet2N02705PlusPointP003RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP003Factor2577
        nodeJet2N02705PlusPointP003Center2577) =
        nodeJet2N02705PlusPointP003Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP003RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP003Rounded2577‖ ≤
          nodeJet2N02705PlusPointP003Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP003Factor2577
      nodeJet2N02705PlusPointP003Center2577)
  rw [nodeJet2N02705PlusPointP003RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP003Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP003Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP003Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP003DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP003Factor2577,
      nodeJet2N02705PlusPointP003Error2577, rounding2542,
      nodeJet2N02705PlusPointP003Radius2577]

theorem nodeJet2N02705PlusPointP003DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP003Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP003RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP003Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP003Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP003Rounded2577]

def nodeJet2N02705PlusPointP004Rounded2577 : RatPair2542 :=
  (((2638192287761769 : ℚ) /
        633825300114114700748351602688),
    (((-5448806790933559) : ℚ) /
        1267650600228229401496703205376))

noncomputable def nodeJet2N02705PlusPointP004Radius2577 : ℝ := ((36572207900331 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705PlusPointP004RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP004Factor2577
        nodeJet2N02705PlusPointP004Center2577) =
        nodeJet2N02705PlusPointP004Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP004RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP004Rounded2577‖ ≤
          nodeJet2N02705PlusPointP004Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP004Factor2577
      nodeJet2N02705PlusPointP004Center2577)
  rw [nodeJet2N02705PlusPointP004RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP004Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP004Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP004Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP004DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP004Factor2577,
      nodeJet2N02705PlusPointP004Error2577, rounding2542,
      nodeJet2N02705PlusPointP004Radius2577]

theorem nodeJet2N02705PlusPointP004DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP004Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP004RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP004Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP004Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP004Rounded2577]

def nodeJet2N02705PlusPointP005Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP005Radius2577 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem nodeJet2N02705PlusPointP005RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP005Factor2577
        nodeJet2N02705PlusPointP005Center2577) =
        nodeJet2N02705PlusPointP005Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP005RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP005Rounded2577‖ ≤
          nodeJet2N02705PlusPointP005Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP005Factor2577
      nodeJet2N02705PlusPointP005Center2577)
  rw [nodeJet2N02705PlusPointP005RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP005Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP005Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP005Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP005DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP005Factor2577,
      nodeJet2N02705PlusPointP005Error2577, rounding2542,
      nodeJet2N02705PlusPointP005Radius2577]

theorem nodeJet2N02705PlusPointP005DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP005Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP005RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP005Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP005Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP005Rounded2577]

def nodeJet2N02705PlusPointP006Rounded2577 : RatPair2542 :=
  (((3 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP006Radius2577 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705PlusPointP006RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP006Factor2577
        nodeJet2N02705PlusPointP006Center2577) =
        nodeJet2N02705PlusPointP006Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP006RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP006Rounded2577‖ ≤
          nodeJet2N02705PlusPointP006Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP006Factor2577
      nodeJet2N02705PlusPointP006Center2577)
  rw [nodeJet2N02705PlusPointP006RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP006Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP006Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP006Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP006DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP006Factor2577,
      nodeJet2N02705PlusPointP006Error2577, rounding2542,
      nodeJet2N02705PlusPointP006Radius2577]

theorem nodeJet2N02705PlusPointP006DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP006Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP006RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP006Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP006Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP006Rounded2577]

def nodeJet2N02705PlusPointP007Rounded2577 : RatPair2542 :=
  (((997798402813 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP007Radius2577 : ℝ := ((2199312797839 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705PlusPointP007RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP007Factor2577
        nodeJet2N02705PlusPointP007Center2577) =
        nodeJet2N02705PlusPointP007Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP007RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP007Rounded2577‖ ≤
          nodeJet2N02705PlusPointP007Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP007Factor2577
      nodeJet2N02705PlusPointP007Center2577)
  rw [nodeJet2N02705PlusPointP007RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP007Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP007Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP007Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP007DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP007Factor2577,
      nodeJet2N02705PlusPointP007Error2577, rounding2542,
      nodeJet2N02705PlusPointP007Radius2577]

theorem nodeJet2N02705PlusPointP007DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP007Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP007RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP007Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP007Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP007Rounded2577]

def nodeJet2N02705PlusPointP008Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP008Radius2577 : ℝ := ((549756427349 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02705PlusPointP008RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP008Factor2577
        nodeJet2N02705PlusPointP008Center2577) =
        nodeJet2N02705PlusPointP008Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP008RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP008Rounded2577‖ ≤
          nodeJet2N02705PlusPointP008Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP008Factor2577
      nodeJet2N02705PlusPointP008Center2577)
  rw [nodeJet2N02705PlusPointP008RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP008Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP008Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP008Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP008DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP008Factor2577,
      nodeJet2N02705PlusPointP008Error2577, rounding2542,
      nodeJet2N02705PlusPointP008Radius2577]

theorem nodeJet2N02705PlusPointP008DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP008Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP008RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP008Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP008Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP008Rounded2577]

def nodeJet2N02705PlusPointP009Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP009Radius2577 : ℝ := ((2199025709425 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705PlusPointP009RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP009Factor2577
        nodeJet2N02705PlusPointP009Center2577) =
        nodeJet2N02705PlusPointP009Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP009RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP009Rounded2577‖ ≤
          nodeJet2N02705PlusPointP009Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP009Factor2577
      nodeJet2N02705PlusPointP009Center2577)
  rw [nodeJet2N02705PlusPointP009RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP009Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP009Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP009Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP009DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP009Factor2577,
      nodeJet2N02705PlusPointP009Error2577, rounding2542,
      nodeJet2N02705PlusPointP009Radius2577]

theorem nodeJet2N02705PlusPointP009DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP009Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP009RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP009Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP009Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP009Rounded2577]

def nodeJet2N02705PlusPointP010Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP010Radius2577 : ℝ := ((2199025709443 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705PlusPointP010RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP010Factor2577
        nodeJet2N02705PlusPointP010Center2577) =
        nodeJet2N02705PlusPointP010Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP010RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP010Rounded2577‖ ≤
          nodeJet2N02705PlusPointP010Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP010Factor2577
      nodeJet2N02705PlusPointP010Center2577)
  rw [nodeJet2N02705PlusPointP010RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP010Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP010Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP010Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP010DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP010Factor2577,
      nodeJet2N02705PlusPointP010Error2577, rounding2542,
      nodeJet2N02705PlusPointP010Radius2577]

theorem nodeJet2N02705PlusPointP010DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP010Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP010RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP010Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP010Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP010Rounded2577]

def nodeJet2N02705PlusPointP011Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP011Radius2577 : ℝ := ((1099512854727 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705PlusPointP011RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP011Factor2577
        nodeJet2N02705PlusPointP011Center2577) =
        nodeJet2N02705PlusPointP011Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP011RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP011Rounded2577‖ ≤
          nodeJet2N02705PlusPointP011Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP011Factor2577
      nodeJet2N02705PlusPointP011Center2577)
  rw [nodeJet2N02705PlusPointP011RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP011Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP011Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP011Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP011DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP011Factor2577,
      nodeJet2N02705PlusPointP011Error2577, rounding2542,
      nodeJet2N02705PlusPointP011Radius2577]

theorem nodeJet2N02705PlusPointP011DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP011Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP011RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP011Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP011Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP011Rounded2577]

def nodeJet2N02705PlusPointP012Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP012Radius2577 : ℝ := ((1099512854733 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705PlusPointP012RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP012Factor2577
        nodeJet2N02705PlusPointP012Center2577) =
        nodeJet2N02705PlusPointP012Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP012RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP012Rounded2577‖ ≤
          nodeJet2N02705PlusPointP012Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP012Factor2577
      nodeJet2N02705PlusPointP012Center2577)
  rw [nodeJet2N02705PlusPointP012RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP012Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP012Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP012Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP012DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP012Factor2577,
      nodeJet2N02705PlusPointP012Error2577, rounding2542,
      nodeJet2N02705PlusPointP012Radius2577]

theorem nodeJet2N02705PlusPointP012DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP012Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP012RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP012Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP012Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP012Rounded2577]

def nodeJet2N02705PlusPointP013Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP013Radius2577 : ℝ := ((2199025709477 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705PlusPointP013RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP013Factor2577
        nodeJet2N02705PlusPointP013Center2577) =
        nodeJet2N02705PlusPointP013Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP013RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP013Rounded2577‖ ≤
          nodeJet2N02705PlusPointP013Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP013Factor2577
      nodeJet2N02705PlusPointP013Center2577)
  rw [nodeJet2N02705PlusPointP013RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP013Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP013Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP013Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP013DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP013Factor2577,
      nodeJet2N02705PlusPointP013Error2577, rounding2542,
      nodeJet2N02705PlusPointP013Radius2577]

theorem nodeJet2N02705PlusPointP013DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP013Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP013RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP013Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP013Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP013Rounded2577]

def nodeJet2N02705PlusPointP014Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP014Radius2577 : ℝ := ((2199025709497 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705PlusPointP014RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP014Factor2577
        nodeJet2N02705PlusPointP014Center2577) =
        nodeJet2N02705PlusPointP014Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP014RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP014Rounded2577‖ ≤
          nodeJet2N02705PlusPointP014Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP014Factor2577
      nodeJet2N02705PlusPointP014Center2577)
  rw [nodeJet2N02705PlusPointP014RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP014Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP014Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP014Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP014DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP014Factor2577,
      nodeJet2N02705PlusPointP014Error2577, rounding2542,
      nodeJet2N02705PlusPointP014Radius2577]

theorem nodeJet2N02705PlusPointP014DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP014Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP014RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP014Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP014Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP014Rounded2577]

def nodeJet2N02705PlusPointP015Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP015Radius2577 : ℝ := ((274878213689 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem nodeJet2N02705PlusPointP015RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP015Factor2577
        nodeJet2N02705PlusPointP015Center2577) =
        nodeJet2N02705PlusPointP015Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP015RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP015Rounded2577‖ ≤
          nodeJet2N02705PlusPointP015Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP015Factor2577
      nodeJet2N02705PlusPointP015Center2577)
  rw [nodeJet2N02705PlusPointP015RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP015Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP015Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP015Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP015DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP015Factor2577,
      nodeJet2N02705PlusPointP015Error2577, rounding2542,
      nodeJet2N02705PlusPointP015Radius2577]

theorem nodeJet2N02705PlusPointP015DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP015Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP015RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP015Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP015Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP015Rounded2577]

def nodeJet2N02705PlusPointP016Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP016Radius2577 : ℝ := ((1099512854761 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705PlusPointP016RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP016Factor2577
        nodeJet2N02705PlusPointP016Center2577) =
        nodeJet2N02705PlusPointP016Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP016RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP016Rounded2577‖ ≤
          nodeJet2N02705PlusPointP016Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP016Factor2577
      nodeJet2N02705PlusPointP016Center2577)
  rw [nodeJet2N02705PlusPointP016RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP016Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP016Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP016Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP016DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP016Factor2577,
      nodeJet2N02705PlusPointP016Error2577, rounding2542,
      nodeJet2N02705PlusPointP016Radius2577]

theorem nodeJet2N02705PlusPointP016DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP016Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP016RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP016Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP016Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP016Rounded2577]

def nodeJet2N02705PlusPointP017Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP017Radius2577 : ℝ := ((1099512854771 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705PlusPointP017RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP017Factor2577
        nodeJet2N02705PlusPointP017Center2577) =
        nodeJet2N02705PlusPointP017Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP017RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP017Rounded2577‖ ≤
          nodeJet2N02705PlusPointP017Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP017Factor2577
      nodeJet2N02705PlusPointP017Center2577)
  rw [nodeJet2N02705PlusPointP017RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP017Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP017Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP017Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP017DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP017Factor2577,
      nodeJet2N02705PlusPointP017Error2577, rounding2542,
      nodeJet2N02705PlusPointP017Radius2577]

theorem nodeJet2N02705PlusPointP017DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP017Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP017RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP017Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP017Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP017Rounded2577]

def nodeJet2N02705PlusPointP018Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP018Radius2577 : ℝ := ((1099512854775 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705PlusPointP018RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP018Factor2577
        nodeJet2N02705PlusPointP018Center2577) =
        nodeJet2N02705PlusPointP018Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP018RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP018Rounded2577‖ ≤
          nodeJet2N02705PlusPointP018Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP018Factor2577
      nodeJet2N02705PlusPointP018Center2577)
  rw [nodeJet2N02705PlusPointP018RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP018Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP018Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP018Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP018DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP018Factor2577,
      nodeJet2N02705PlusPointP018Error2577, rounding2542,
      nodeJet2N02705PlusPointP018Radius2577]

theorem nodeJet2N02705PlusPointP018DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP018Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP018RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP018Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP018Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP018Rounded2577]

def nodeJet2N02705PlusPointP019Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP019Radius2577 : ℝ := ((549756427391 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02705PlusPointP019RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP019Factor2577
        nodeJet2N02705PlusPointP019Center2577) =
        nodeJet2N02705PlusPointP019Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP019RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP019Rounded2577‖ ≤
          nodeJet2N02705PlusPointP019Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP019Factor2577
      nodeJet2N02705PlusPointP019Center2577)
  rw [nodeJet2N02705PlusPointP019RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP019Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP019Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP019Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP019DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP019Factor2577,
      nodeJet2N02705PlusPointP019Error2577, rounding2542,
      nodeJet2N02705PlusPointP019Radius2577]

theorem nodeJet2N02705PlusPointP019DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP019Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP019RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP019Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP019Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP019Rounded2577]

def nodeJet2N02705PlusPointP020Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP020Radius2577 : ℝ := ((2199025709579 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705PlusPointP020RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP020Factor2577
        nodeJet2N02705PlusPointP020Center2577) =
        nodeJet2N02705PlusPointP020Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP020RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP020Rounded2577‖ ≤
          nodeJet2N02705PlusPointP020Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP020Factor2577
      nodeJet2N02705PlusPointP020Center2577)
  rw [nodeJet2N02705PlusPointP020RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP020Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP020Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP020Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP020DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP020Factor2577,
      nodeJet2N02705PlusPointP020Error2577, rounding2542,
      nodeJet2N02705PlusPointP020Radius2577]

theorem nodeJet2N02705PlusPointP020DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP020Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP020RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP020Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP020Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP020Rounded2577]

def nodeJet2N02705PlusPointP021Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP021Radius2577 : ℝ := ((2199025709591 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705PlusPointP021RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP021Factor2577
        nodeJet2N02705PlusPointP021Center2577) =
        nodeJet2N02705PlusPointP021Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP021RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP021Rounded2577‖ ≤
          nodeJet2N02705PlusPointP021Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP021Factor2577
      nodeJet2N02705PlusPointP021Center2577)
  rw [nodeJet2N02705PlusPointP021RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP021Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP021Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP021Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP021DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP021Factor2577,
      nodeJet2N02705PlusPointP021Error2577, rounding2542,
      nodeJet2N02705PlusPointP021Radius2577]

theorem nodeJet2N02705PlusPointP021DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP021Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP021RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP021Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP021Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP021Rounded2577]

def nodeJet2N02705PlusPointP022Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP022Radius2577 : ℝ := ((1099512854799 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705PlusPointP022RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP022Factor2577
        nodeJet2N02705PlusPointP022Center2577) =
        nodeJet2N02705PlusPointP022Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP022RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP022Rounded2577‖ ≤
          nodeJet2N02705PlusPointP022Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP022Factor2577
      nodeJet2N02705PlusPointP022Center2577)
  rw [nodeJet2N02705PlusPointP022RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP022Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP022Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP022Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP022DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP022Factor2577,
      nodeJet2N02705PlusPointP022Error2577, rounding2542,
      nodeJet2N02705PlusPointP022Radius2577]

theorem nodeJet2N02705PlusPointP022DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP022Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP022RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP022Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP022Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP022Rounded2577]

def nodeJet2N02705PlusPointP023Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP023Radius2577 : ℝ := ((137439106851 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem nodeJet2N02705PlusPointP023RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP023Factor2577
        nodeJet2N02705PlusPointP023Center2577) =
        nodeJet2N02705PlusPointP023Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP023RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP023Rounded2577‖ ≤
          nodeJet2N02705PlusPointP023Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP023Factor2577
      nodeJet2N02705PlusPointP023Center2577)
  rw [nodeJet2N02705PlusPointP023RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP023Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP023Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP023Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP023DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP023Factor2577,
      nodeJet2N02705PlusPointP023Error2577, rounding2542,
      nodeJet2N02705PlusPointP023Radius2577]

theorem nodeJet2N02705PlusPointP023DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP023Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP023RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP023Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP023Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP023Rounded2577]

def nodeJet2N02705PlusPointP024Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP024Radius2577 : ℝ := ((2199025709625 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705PlusPointP024RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP024Factor2577
        nodeJet2N02705PlusPointP024Center2577) =
        nodeJet2N02705PlusPointP024Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP024RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP024Rounded2577‖ ≤
          nodeJet2N02705PlusPointP024Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP024Factor2577
      nodeJet2N02705PlusPointP024Center2577)
  rw [nodeJet2N02705PlusPointP024RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP024Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP024Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP024Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP024DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP024Factor2577,
      nodeJet2N02705PlusPointP024Error2577, rounding2542,
      nodeJet2N02705PlusPointP024Radius2577]

theorem nodeJet2N02705PlusPointP024DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP024Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP024RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP024Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP024Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP024Rounded2577]

def nodeJet2N02705PlusPointP025Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP025Radius2577 : ℝ := ((2199025709635 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem nodeJet2N02705PlusPointP025RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP025Factor2577
        nodeJet2N02705PlusPointP025Center2577) =
        nodeJet2N02705PlusPointP025Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP025RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP025Rounded2577‖ ≤
          nodeJet2N02705PlusPointP025Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP025Factor2577
      nodeJet2N02705PlusPointP025Center2577)
  rw [nodeJet2N02705PlusPointP025RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP025Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP025Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP025Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP025DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP025Factor2577,
      nodeJet2N02705PlusPointP025Error2577, rounding2542,
      nodeJet2N02705PlusPointP025Radius2577]

theorem nodeJet2N02705PlusPointP025DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP025Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP025RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP025Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP025Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP025Rounded2577]

def nodeJet2N02705PlusPointP026Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP026Radius2577 : ℝ := ((1099512854823 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705PlusPointP026RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP026Factor2577
        nodeJet2N02705PlusPointP026Center2577) =
        nodeJet2N02705PlusPointP026Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP026RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP026Rounded2577‖ ≤
          nodeJet2N02705PlusPointP026Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP026Factor2577
      nodeJet2N02705PlusPointP026Center2577)
  rw [nodeJet2N02705PlusPointP026RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP026Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP026Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP026Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP026DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP026Factor2577,
      nodeJet2N02705PlusPointP026Error2577, rounding2542,
      nodeJet2N02705PlusPointP026Radius2577]

theorem nodeJet2N02705PlusPointP026DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP026Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP026RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP026Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP026Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP026Rounded2577]

def nodeJet2N02705PlusPointP027Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP027Radius2577 : ℝ := ((1099512854831 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705PlusPointP027RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP027Factor2577
        nodeJet2N02705PlusPointP027Center2577) =
        nodeJet2N02705PlusPointP027Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP027RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP027Rounded2577‖ ≤
          nodeJet2N02705PlusPointP027Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP027Factor2577
      nodeJet2N02705PlusPointP027Center2577)
  rw [nodeJet2N02705PlusPointP027RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP027Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP027Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP027Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP027DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP027Factor2577,
      nodeJet2N02705PlusPointP027Error2577, rounding2542,
      nodeJet2N02705PlusPointP027Radius2577]

theorem nodeJet2N02705PlusPointP027DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP027Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP027RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP027Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP027Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP027Rounded2577]

def nodeJet2N02705PlusPointP028Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP028Radius2577 : ℝ := ((549756427417 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem nodeJet2N02705PlusPointP028RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP028Factor2577
        nodeJet2N02705PlusPointP028Center2577) =
        nodeJet2N02705PlusPointP028Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP028RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP028Rounded2577‖ ≤
          nodeJet2N02705PlusPointP028Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP028Factor2577
      nodeJet2N02705PlusPointP028Center2577)
  rw [nodeJet2N02705PlusPointP028RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP028Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP028Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP028Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP028DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP028Factor2577,
      nodeJet2N02705PlusPointP028Error2577, rounding2542,
      nodeJet2N02705PlusPointP028Radius2577]

theorem nodeJet2N02705PlusPointP028DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP028Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP028RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP028Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP028Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP028Rounded2577]

def nodeJet2N02705PlusPointP029Rounded2577 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705PlusPointP029Radius2577 : ℝ := ((1099512854839 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem nodeJet2N02705PlusPointP029RoundCompute2577 :
    pairRound2542 (pairMul2542 nodeJet2N02705PlusPointP029Factor2577
        nodeJet2N02705PlusPointP029Center2577) =
        nodeJet2N02705PlusPointP029Rounded2577 := by
  cbv

theorem nodeJet2N02705PlusPointP029RoundedError2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02705PlusPointPosition2577 -
      embedPair2542 nodeJet2N02705PlusPointP029Rounded2577‖ ≤
          nodeJet2N02705PlusPointP029Radius2577 := by
  have hr := embedPair_round_error2542 (pairMul2542 nodeJet2N02705PlusPointP029Factor2577
      nodeJet2N02705PlusPointP029Center2577)
  rw [nodeJet2N02705PlusPointP029RoundCompute2577, embedPair_mul2542] at hr
  have h := (nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP029Factor2577 * embedPair2542
        nodeJet2N02705PlusPointP029Center2577)
    (embedPair2542 nodeJet2N02705PlusPointP029Rounded2577)).trans (add_le_add
        nodeJet2N02705PlusPointP029DerivativeError2577 hr)
  apply h.trans
  norm_num [pairMagnitude2542, nodeJet2N02705PlusPointP029Factor2577,
      nodeJet2N02705PlusPointP029Error2577, rounding2542,
      nodeJet2N02705PlusPointP029Radius2577]

theorem nodeJet2N02705PlusPointP029DerivativeNorm2577 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02705PlusPointPosition2577‖ ≤ 1 := by
  have h := nodeJet2N02705PlusPoint_triangle2577
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02705PlusPointPosition2577)
    (embedPair2542 nodeJet2N02705PlusPointP029Rounded2577) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add nodeJet2N02705PlusPointP029RoundedError2577
      (embedPair_magnitude2542
      nodeJet2N02705PlusPointP029Rounded2577))
  apply h'.trans
  norm_num [nodeJet2N02705PlusPointP029Radius2577, pairMagnitude2542,
      nodeJet2N02705PlusPointP029Rounded2577]

noncomputable def nodeJet2N02705PlusSignedValue2577 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 nodeJet2N02705PlusPointP000Rounded2577
  | 1 => embedPair2542 nodeJet2N02705PlusPointP001Rounded2577
  | 2 => embedPair2542 nodeJet2N02705PlusPointP002Rounded2577
  | 3 => embedPair2542 nodeJet2N02705PlusPointP003Rounded2577
  | 4 => embedPair2542 nodeJet2N02705PlusPointP004Rounded2577
  | 5 => embedPair2542 nodeJet2N02705PlusPointP005Rounded2577
  | 6 => embedPair2542 nodeJet2N02705PlusPointP006Rounded2577
  | 7 => embedPair2542 nodeJet2N02705PlusPointP007Rounded2577
  | 8 => embedPair2542 nodeJet2N02705PlusPointP008Rounded2577
  | 9 => embedPair2542 nodeJet2N02705PlusPointP009Rounded2577
  | 10 => embedPair2542 nodeJet2N02705PlusPointP010Rounded2577
  | 11 => embedPair2542 nodeJet2N02705PlusPointP011Rounded2577
  | 12 => embedPair2542 nodeJet2N02705PlusPointP012Rounded2577
  | 13 => embedPair2542 nodeJet2N02705PlusPointP013Rounded2577
  | 14 => embedPair2542 nodeJet2N02705PlusPointP014Rounded2577
  | 15 => embedPair2542 nodeJet2N02705PlusPointP015Rounded2577
  | 16 => embedPair2542 nodeJet2N02705PlusPointP016Rounded2577
  | 17 => embedPair2542 nodeJet2N02705PlusPointP017Rounded2577
  | 18 => embedPair2542 nodeJet2N02705PlusPointP018Rounded2577
  | 19 => embedPair2542 nodeJet2N02705PlusPointP019Rounded2577
  | 20 => embedPair2542 nodeJet2N02705PlusPointP020Rounded2577
  | 21 => embedPair2542 nodeJet2N02705PlusPointP021Rounded2577
  | 22 => embedPair2542 nodeJet2N02705PlusPointP022Rounded2577
  | 23 => embedPair2542 nodeJet2N02705PlusPointP023Rounded2577
  | 24 => embedPair2542 nodeJet2N02705PlusPointP024Rounded2577
  | 25 => embedPair2542 nodeJet2N02705PlusPointP025Rounded2577
  | 26 => embedPair2542 nodeJet2N02705PlusPointP026Rounded2577
  | 27 => embedPair2542 nodeJet2N02705PlusPointP027Rounded2577
  | 28 => embedPair2542 nodeJet2N02705PlusPointP028Rounded2577
  | 29 => embedPair2542 nodeJet2N02705PlusPointP029Rounded2577
  | _ => 0

noncomputable def nodeJet2N02705PlusSignedError2577 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => nodeJet2N02705PlusPointP000Radius2577
  | 1 => nodeJet2N02705PlusPointP001Radius2577
  | 2 => nodeJet2N02705PlusPointP002Radius2577
  | 3 => nodeJet2N02705PlusPointP003Radius2577
  | 4 => nodeJet2N02705PlusPointP004Radius2577
  | 5 => nodeJet2N02705PlusPointP005Radius2577
  | 6 => nodeJet2N02705PlusPointP006Radius2577
  | 7 => nodeJet2N02705PlusPointP007Radius2577
  | 8 => nodeJet2N02705PlusPointP008Radius2577
  | 9 => nodeJet2N02705PlusPointP009Radius2577
  | 10 => nodeJet2N02705PlusPointP010Radius2577
  | 11 => nodeJet2N02705PlusPointP011Radius2577
  | 12 => nodeJet2N02705PlusPointP012Radius2577
  | 13 => nodeJet2N02705PlusPointP013Radius2577
  | 14 => nodeJet2N02705PlusPointP014Radius2577
  | 15 => nodeJet2N02705PlusPointP015Radius2577
  | 16 => nodeJet2N02705PlusPointP016Radius2577
  | 17 => nodeJet2N02705PlusPointP017Radius2577
  | 18 => nodeJet2N02705PlusPointP018Radius2577
  | 19 => nodeJet2N02705PlusPointP019Radius2577
  | 20 => nodeJet2N02705PlusPointP020Radius2577
  | 21 => nodeJet2N02705PlusPointP021Radius2577
  | 22 => nodeJet2N02705PlusPointP022Radius2577
  | 23 => nodeJet2N02705PlusPointP023Radius2577
  | 24 => nodeJet2N02705PlusPointP024Radius2577
  | 25 => nodeJet2N02705PlusPointP025Radius2577
  | 26 => nodeJet2N02705PlusPointP026Radius2577
  | 27 => nodeJet2N02705PlusPointP027Radius2577
  | 28 => nodeJet2N02705PlusPointP028Radius2577
  | 29 => nodeJet2N02705PlusPointP029Radius2577
  | _ => 0

theorem nodeJet2N02705PlusSignedExpError2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02705PlusPointPosition2577 -
        nodeJet2N02705PlusSignedValue2577 i‖ ≤ nodeJet2N02705PlusSignedError2577 i := by
  fin_cases i
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP000RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP001RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP002RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP003RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP004RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP005RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP006RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP007RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP008RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP009RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP010RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP011RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP012RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP013RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP014RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP015RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP016RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP017RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP018RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP019RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP020RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP021RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP022RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP023RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP024RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP025RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP026RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP027RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP028RoundedError2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP029RoundedError2577

theorem nodeJet2N02705PlusSignedUnitNorm2577 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02705PlusPointPosition2577‖ ≤ 1 :=
        by
  fin_cases i
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP000DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP001DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP002DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP003DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP004DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP005DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP006DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP007DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP008DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP009DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP010DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP011DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP012DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP013DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP014DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP015DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP016DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP017DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP018DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP019DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP020DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP021DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP022DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP023DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP024DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP025DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP026DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP027DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP028DerivativeNorm2577
  · simpa only [nodeJet2N02705PlusSignedValue2577, nodeJet2N02705PlusSignedError2577] using
      nodeJet2N02705PlusPointP029DerivativeNorm2577

noncomputable def nodeJet2N02705PlusSignedSum2577 : ℂ := ⟨(((-(((714760558239 * 10^40
        + 693805342499455617728773225930202966192) * 10^40
        + 8842399781329320306806088080814301340617) * 10^40
        + 9559025075856786170577216768047269991795)) : ℝ) /
        (((709803441694 * 10^40
        + 9286040520740311406294280797278912962090) * 10^40
        + 4324364277263734305479824015949823344796) * 10^40
        + 2659731992932150006119314388217384402944)),
    (((((833329354064 * 10^40
        + 6993571717420145813172956527325422201662) * 10^40
        + 9185379056215595017613361297932391128561) * 10^40
        + 1904709051654915571517337831636565977605) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888))⟩

noncomputable def nodeJet2N02705PlusSignedUpper2577 : ℝ := ((116559093 : ℝ) /
        100000000)

theorem nodeJet2N02705PlusSignedSum_eq2577 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02705PlusSignedValue2577 i) =
      nodeJet2N02705PlusSignedSum2577 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        nodeJet2N02705PlusSignedValue2577,
      nodeJet2N02705PlusSignedSum2577, embedPair2542, nodeJet2N02705PlusPointP000Rounded2577,
      nodeJet2N02705PlusPointP001Rounded2577,
      nodeJet2N02705PlusPointP002Rounded2577,
      nodeJet2N02705PlusPointP003Rounded2577,
      nodeJet2N02705PlusPointP004Rounded2577,
      nodeJet2N02705PlusPointP005Rounded2577,
      nodeJet2N02705PlusPointP006Rounded2577,
      nodeJet2N02705PlusPointP007Rounded2577,
      nodeJet2N02705PlusPointP008Rounded2577,
      nodeJet2N02705PlusPointP009Rounded2577,
      nodeJet2N02705PlusPointP010Rounded2577,
      nodeJet2N02705PlusPointP011Rounded2577,
      nodeJet2N02705PlusPointP012Rounded2577,
      nodeJet2N02705PlusPointP013Rounded2577,
      nodeJet2N02705PlusPointP014Rounded2577,
      nodeJet2N02705PlusPointP015Rounded2577,
      nodeJet2N02705PlusPointP016Rounded2577,
      nodeJet2N02705PlusPointP017Rounded2577,
      nodeJet2N02705PlusPointP018Rounded2577,
      nodeJet2N02705PlusPointP019Rounded2577,
      nodeJet2N02705PlusPointP020Rounded2577,
      nodeJet2N02705PlusPointP021Rounded2577,
      nodeJet2N02705PlusPointP022Rounded2577,
      nodeJet2N02705PlusPointP023Rounded2577,
      nodeJet2N02705PlusPointP024Rounded2577,
      nodeJet2N02705PlusPointP025Rounded2577,
      nodeJet2N02705PlusPointP026Rounded2577,
      nodeJet2N02705PlusPointP027Rounded2577,
      nodeJet2N02705PlusPointP028Rounded2577,
      nodeJet2N02705PlusPointP029Rounded2577, Complex.mul_re, Complex.mul_im]

theorem nodeJet2N02705PlusSignedSum_norm2577 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02705PlusSignedValue2577 i‖ ≤
        ((116559083 :
        ℝ) /
        100000000) := by
  rw [nodeJet2N02705PlusSignedSum_eq2577]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [nodeJet2N02705PlusSignedSum2577]

theorem nodeJet2N02705PlusSignedCharge2577 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02705PlusSignedError2577 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      nodeJet2N02705PlusSignedError2577, nodeJet2N02705PlusPointP000Radius2577,
      nodeJet2N02705PlusPointP001Radius2577,
      nodeJet2N02705PlusPointP002Radius2577,
      nodeJet2N02705PlusPointP003Radius2577,
      nodeJet2N02705PlusPointP004Radius2577,
      nodeJet2N02705PlusPointP005Radius2577,
      nodeJet2N02705PlusPointP006Radius2577,
      nodeJet2N02705PlusPointP007Radius2577,
      nodeJet2N02705PlusPointP008Radius2577,
      nodeJet2N02705PlusPointP009Radius2577,
      nodeJet2N02705PlusPointP010Radius2577,
      nodeJet2N02705PlusPointP011Radius2577,
      nodeJet2N02705PlusPointP012Radius2577,
      nodeJet2N02705PlusPointP013Radius2577,
      nodeJet2N02705PlusPointP014Radius2577,
      nodeJet2N02705PlusPointP015Radius2577,
      nodeJet2N02705PlusPointP016Radius2577,
      nodeJet2N02705PlusPointP017Radius2577,
      nodeJet2N02705PlusPointP018Radius2577,
      nodeJet2N02705PlusPointP019Radius2577,
      nodeJet2N02705PlusPointP020Radius2577,
      nodeJet2N02705PlusPointP021Radius2577,
      nodeJet2N02705PlusPointP022Radius2577,
      nodeJet2N02705PlusPointP023Radius2577,
      nodeJet2N02705PlusPointP024Radius2577,
      nodeJet2N02705PlusPointP025Radius2577,
      nodeJet2N02705PlusPointP026Radius2577,
      nodeJet2N02705PlusPointP027Radius2577,
      nodeJet2N02705PlusPointP028Radius2577,
      nodeJet2N02705PlusPointP029Radius2577]

theorem nodeJet2N02705PlusSignedUpper_le2577 :
    signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 nodeJet2N02705PlusPointPosition2577 ≤ nodeJet2N02705PlusSignedUpper2577
          := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02705PlusPointPosition2577‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * nodeJet2N02705PlusSignedValue2577 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * nodeJet2N02705PlusSignedError2577 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (nodeJet2N02705PlusSignedExpError2577
        i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02705PlusPointPosition2577‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (nodeJet2N02705PlusSignedUnitNorm2577 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i nodeJet2N02705PlusPointPosition2577‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 nodeJet2N02705PlusSignedUpper2577
  linarith [nodeJet2N02705PlusSignedSum_norm2577, nodeJet2N02705PlusSignedCharge2577]

theorem nodeJet2N02705PlusPhysical2577 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        nodeJet2N02705PlusPointPosition2577‖ ≤
      nodeJet2N02705PlusSignedUpper2577 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        nodeJet2N02705PlusPointPosition2577
  exact h.trans nodeJet2N02705PlusSignedUpper_le2577

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.nodeJet2N02705PlusSignedExpError2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02705PlusSignedSum_eq2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02705PlusSignedCharge2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02705PlusSignedUpper_le2577
#print axioms ConnesWeilRH.Dev.nodeJet2N02705PlusPhysical2577
