import ConnesWeilRH.Dev.C1RouteASharedSecondN02701MinusDerivatives2576
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem sharedSecondN02701MinusPoint_triangle2576 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def sharedSecondN02701MinusPointP000Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP000Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02701MinusPointP000RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP000Factor2576
        sharedSecondN02701MinusPointP000Center2576) =
        sharedSecondN02701MinusPointP000Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP000RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP000Rounded2576‖ ≤
          sharedSecondN02701MinusPointP000Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP000Factor2576
      sharedSecondN02701MinusPointP000Center2576)
  rw [sharedSecondN02701MinusPointP000RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP000Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP000Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP000Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP000DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP000Factor2576,
      sharedSecondN02701MinusPointP000Error2576, rounding2542,
      sharedSecondN02701MinusPointP000Radius2576]

theorem sharedSecondN02701MinusPointP000DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP000Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP000RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP000Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP000Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP000Rounded2576]

def sharedSecondN02701MinusPointP001Rounded2576 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP001Radius2576 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02701MinusPointP001RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP001Factor2576
        sharedSecondN02701MinusPointP001Center2576) =
        sharedSecondN02701MinusPointP001Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP001RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP001Rounded2576‖ ≤
          sharedSecondN02701MinusPointP001Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP001Factor2576
      sharedSecondN02701MinusPointP001Center2576)
  rw [sharedSecondN02701MinusPointP001RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP001Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP001Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP001Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP001DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP001Factor2576,
      sharedSecondN02701MinusPointP001Error2576, rounding2542,
      sharedSecondN02701MinusPointP001Radius2576]

theorem sharedSecondN02701MinusPointP001DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP001Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP001RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP001Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP001Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP001Rounded2576]

def sharedSecondN02701MinusPointP002Rounded2576 : RatPair2542 :=
  (((30801705 : ℚ) /
        1267650600228229401496703205376),
    (((-21706931) : ℚ) /
        1267650600228229401496703205376))

noncomputable def sharedSecondN02701MinusPointP002Radius2576 : ℝ := ((2199023397881 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02701MinusPointP002RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP002Factor2576
        sharedSecondN02701MinusPointP002Center2576) =
        sharedSecondN02701MinusPointP002Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP002RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP002Rounded2576‖ ≤
          sharedSecondN02701MinusPointP002Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP002Factor2576
      sharedSecondN02701MinusPointP002Center2576)
  rw [sharedSecondN02701MinusPointP002RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP002Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP002Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP002Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP002DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP002Factor2576,
      sharedSecondN02701MinusPointP002Error2576, rounding2542,
      sharedSecondN02701MinusPointP002Radius2576]

theorem sharedSecondN02701MinusPointP002DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP002Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP002RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP002Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP002Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP002Rounded2576]

def sharedSecondN02701MinusPointP003Rounded2576 : RatPair2542 :=
  (((332658606788883 : ℚ) /
        1267650600228229401496703205376),
    ((26789416028431 : ℚ) /
        316912650057057350374175801344))

noncomputable def sharedSecondN02701MinusPointP003Radius2576 : ℝ := ((243242258949 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem sharedSecondN02701MinusPointP003RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP003Factor2576
        sharedSecondN02701MinusPointP003Center2576) =
        sharedSecondN02701MinusPointP003Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP003RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP003Rounded2576‖ ≤
          sharedSecondN02701MinusPointP003Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP003Factor2576
      sharedSecondN02701MinusPointP003Center2576)
  rw [sharedSecondN02701MinusPointP003RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP003Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP003Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP003Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP003DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP003Factor2576,
      sharedSecondN02701MinusPointP003Error2576, rounding2542,
      sharedSecondN02701MinusPointP003Radius2576]

theorem sharedSecondN02701MinusPointP003DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP003Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP003RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP003Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP003Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP003Rounded2576]

def sharedSecondN02701MinusPointP004Rounded2576 : RatPair2542 :=
  (((63726098544575275 : ℚ) /
        633825300114114700748351602688),
    (((-96574797251820649) : ℚ) /
        1267650600228229401496703205376))

noncomputable def sharedSecondN02701MinusPointP004Radius2576 : ℝ := ((343666169645335 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem sharedSecondN02701MinusPointP004RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP004Factor2576
        sharedSecondN02701MinusPointP004Center2576) =
        sharedSecondN02701MinusPointP004Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP004RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP004Rounded2576‖ ≤
          sharedSecondN02701MinusPointP004Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP004Factor2576
      sharedSecondN02701MinusPointP004Center2576)
  rw [sharedSecondN02701MinusPointP004RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP004Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP004Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP004Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP004DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP004Factor2576,
      sharedSecondN02701MinusPointP004Error2576, rounding2542,
      sharedSecondN02701MinusPointP004Radius2576]

theorem sharedSecondN02701MinusPointP004DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP004Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP004RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP004Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP004Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP004Rounded2576]

def sharedSecondN02701MinusPointP005Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP005Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02701MinusPointP005RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP005Factor2576
        sharedSecondN02701MinusPointP005Center2576) =
        sharedSecondN02701MinusPointP005Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP005RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP005Rounded2576‖ ≤
          sharedSecondN02701MinusPointP005Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP005Factor2576
      sharedSecondN02701MinusPointP005Center2576)
  rw [sharedSecondN02701MinusPointP005RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP005Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP005Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP005Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP005DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP005Factor2576,
      sharedSecondN02701MinusPointP005Error2576, rounding2542,
      sharedSecondN02701MinusPointP005Radius2576]

theorem sharedSecondN02701MinusPointP005DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP005Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP005RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP005Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP005Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP005Rounded2576]

def sharedSecondN02701MinusPointP006Rounded2576 : RatPair2542 :=
  (((23 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP006Radius2576 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02701MinusPointP006RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP006Factor2576
        sharedSecondN02701MinusPointP006Center2576) =
        sharedSecondN02701MinusPointP006Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP006RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP006Rounded2576‖ ≤
          sharedSecondN02701MinusPointP006Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP006Factor2576
      sharedSecondN02701MinusPointP006Center2576)
  rw [sharedSecondN02701MinusPointP006RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP006Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP006Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP006Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP006DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP006Factor2576,
      sharedSecondN02701MinusPointP006Error2576, rounding2542,
      sharedSecondN02701MinusPointP006Radius2576]

theorem sharedSecondN02701MinusPointP006DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP006Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP006RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP006Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP006Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP006Rounded2576]

def sharedSecondN02701MinusPointP007Rounded2576 : RatPair2542 :=
  (((35569883721463 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP007Radius2576 : ℝ := ((2203946193261 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02701MinusPointP007RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP007Factor2576
        sharedSecondN02701MinusPointP007Center2576) =
        sharedSecondN02701MinusPointP007Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP007RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP007Rounded2576‖ ≤
          sharedSecondN02701MinusPointP007Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP007Factor2576
      sharedSecondN02701MinusPointP007Center2576)
  rw [sharedSecondN02701MinusPointP007RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP007Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP007Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP007Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP007DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP007Factor2576,
      sharedSecondN02701MinusPointP007Error2576, rounding2542,
      sharedSecondN02701MinusPointP007Radius2576]

theorem sharedSecondN02701MinusPointP007DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP007Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP007RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP007Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP007Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP007Rounded2576]

def sharedSecondN02701MinusPointP008Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP008Radius2576 : ℝ := ((1100278695965 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem sharedSecondN02701MinusPointP008RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP008Factor2576
        sharedSecondN02701MinusPointP008Center2576) =
        sharedSecondN02701MinusPointP008Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP008RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP008Rounded2576‖ ≤
          sharedSecondN02701MinusPointP008Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP008Factor2576
      sharedSecondN02701MinusPointP008Center2576)
  rw [sharedSecondN02701MinusPointP008RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP008Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP008Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP008Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP008DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP008Factor2576,
      sharedSecondN02701MinusPointP008Error2576, rounding2542,
      sharedSecondN02701MinusPointP008Radius2576]

theorem sharedSecondN02701MinusPointP008DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP008Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP008RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP008Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP008Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP008Rounded2576]

def sharedSecondN02701MinusPointP009Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP009Radius2576 : ℝ := ((2200557392675 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02701MinusPointP009RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP009Factor2576
        sharedSecondN02701MinusPointP009Center2576) =
        sharedSecondN02701MinusPointP009Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP009RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP009Rounded2576‖ ≤
          sharedSecondN02701MinusPointP009Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP009Factor2576
      sharedSecondN02701MinusPointP009Center2576)
  rw [sharedSecondN02701MinusPointP009RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP009Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP009Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP009Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP009DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP009Factor2576,
      sharedSecondN02701MinusPointP009Error2576, rounding2542,
      sharedSecondN02701MinusPointP009Radius2576]

theorem sharedSecondN02701MinusPointP009DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP009Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP009RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP009Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP009Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP009Rounded2576]

def sharedSecondN02701MinusPointP010Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP010Radius2576 : ℝ := ((1100278696553 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem sharedSecondN02701MinusPointP010RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP010Factor2576
        sharedSecondN02701MinusPointP010Center2576) =
        sharedSecondN02701MinusPointP010Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP010RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP010Rounded2576‖ ≤
          sharedSecondN02701MinusPointP010Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP010Factor2576
      sharedSecondN02701MinusPointP010Center2576)
  rw [sharedSecondN02701MinusPointP010RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP010Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP010Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP010Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP010DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP010Factor2576,
      sharedSecondN02701MinusPointP010Error2576, rounding2542,
      sharedSecondN02701MinusPointP010Radius2576]

theorem sharedSecondN02701MinusPointP010DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP010Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP010RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP010Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP010Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP010Rounded2576]

def sharedSecondN02701MinusPointP011Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP011Radius2576 : ℝ := ((1100278696697 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem sharedSecondN02701MinusPointP011RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP011Factor2576
        sharedSecondN02701MinusPointP011Center2576) =
        sharedSecondN02701MinusPointP011Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP011RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP011Rounded2576‖ ≤
          sharedSecondN02701MinusPointP011Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP011Factor2576
      sharedSecondN02701MinusPointP011Center2576)
  rw [sharedSecondN02701MinusPointP011RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP011Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP011Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP011Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP011DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP011Factor2576,
      sharedSecondN02701MinusPointP011Error2576, rounding2542,
      sharedSecondN02701MinusPointP011Radius2576]

theorem sharedSecondN02701MinusPointP011DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP011Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP011RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP011Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP011Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP011Rounded2576]

def sharedSecondN02701MinusPointP012Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP012Radius2576 : ℝ := ((550139348423 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem sharedSecondN02701MinusPointP012RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP012Factor2576
        sharedSecondN02701MinusPointP012Center2576) =
        sharedSecondN02701MinusPointP012Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP012RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP012Rounded2576‖ ≤
          sharedSecondN02701MinusPointP012Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP012Factor2576
      sharedSecondN02701MinusPointP012Center2576)
  rw [sharedSecondN02701MinusPointP012RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP012Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP012Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP012Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP012DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP012Factor2576,
      sharedSecondN02701MinusPointP012Error2576, rounding2542,
      sharedSecondN02701MinusPointP012Radius2576]

theorem sharedSecondN02701MinusPointP012DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP012Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP012RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP012Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP012Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP012Rounded2576]

def sharedSecondN02701MinusPointP013Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP013Radius2576 : ℝ := ((550139348491 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem sharedSecondN02701MinusPointP013RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP013Factor2576
        sharedSecondN02701MinusPointP013Center2576) =
        sharedSecondN02701MinusPointP013Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP013RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP013Rounded2576‖ ≤
          sharedSecondN02701MinusPointP013Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP013Factor2576
      sharedSecondN02701MinusPointP013Center2576)
  rw [sharedSecondN02701MinusPointP013RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP013Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP013Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP013Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP013DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP013Factor2576,
      sharedSecondN02701MinusPointP013Error2576, rounding2542,
      sharedSecondN02701MinusPointP013Radius2576]

theorem sharedSecondN02701MinusPointP013DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP013Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP013RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP013Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP013Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP013Rounded2576]

def sharedSecondN02701MinusPointP014Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP014Radius2576 : ℝ := ((2200557394467 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02701MinusPointP014RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP014Factor2576
        sharedSecondN02701MinusPointP014Center2576) =
        sharedSecondN02701MinusPointP014Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP014RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP014Rounded2576‖ ≤
          sharedSecondN02701MinusPointP014Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP014Factor2576
      sharedSecondN02701MinusPointP014Center2576)
  rw [sharedSecondN02701MinusPointP014RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP014Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP014Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP014Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP014DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP014Factor2576,
      sharedSecondN02701MinusPointP014Error2576, rounding2542,
      sharedSecondN02701MinusPointP014Radius2576]

theorem sharedSecondN02701MinusPointP014DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP014Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP014RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP014Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP014Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP014Rounded2576]

def sharedSecondN02701MinusPointP015Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP015Radius2576 : ℝ := ((550139348707 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem sharedSecondN02701MinusPointP015RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP015Factor2576
        sharedSecondN02701MinusPointP015Center2576) =
        sharedSecondN02701MinusPointP015Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP015RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP015Rounded2576‖ ≤
          sharedSecondN02701MinusPointP015Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP015Factor2576
      sharedSecondN02701MinusPointP015Center2576)
  rw [sharedSecondN02701MinusPointP015RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP015Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP015Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP015Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP015DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP015Factor2576,
      sharedSecondN02701MinusPointP015Error2576, rounding2542,
      sharedSecondN02701MinusPointP015Radius2576]

theorem sharedSecondN02701MinusPointP015DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP015Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP015RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP015Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP015Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP015Rounded2576]

def sharedSecondN02701MinusPointP016Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP016Radius2576 : ℝ := ((137534837193 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem sharedSecondN02701MinusPointP016RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP016Factor2576
        sharedSecondN02701MinusPointP016Center2576) =
        sharedSecondN02701MinusPointP016Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP016RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP016Rounded2576‖ ≤
          sharedSecondN02701MinusPointP016Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP016Factor2576
      sharedSecondN02701MinusPointP016Center2576)
  rw [sharedSecondN02701MinusPointP016RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP016Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP016Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP016Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP016DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP016Factor2576,
      sharedSecondN02701MinusPointP016Error2576, rounding2542,
      sharedSecondN02701MinusPointP016Radius2576]

theorem sharedSecondN02701MinusPointP016DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP016Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP016RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP016Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP016Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP016Rounded2576]

def sharedSecondN02701MinusPointP017Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP017Radius2576 : ℝ := ((1100278697797 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem sharedSecondN02701MinusPointP017RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP017Factor2576
        sharedSecondN02701MinusPointP017Center2576) =
        sharedSecondN02701MinusPointP017Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP017RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP017Rounded2576‖ ≤
          sharedSecondN02701MinusPointP017Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP017Factor2576
      sharedSecondN02701MinusPointP017Center2576)
  rw [sharedSecondN02701MinusPointP017RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP017Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP017Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP017Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP017DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP017Factor2576,
      sharedSecondN02701MinusPointP017Error2576, rounding2542,
      sharedSecondN02701MinusPointP017Radius2576]

theorem sharedSecondN02701MinusPointP017DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP017Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP017RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP017Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP017Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP017Rounded2576]

def sharedSecondN02701MinusPointP018Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP018Radius2576 : ℝ := ((1100278697893 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem sharedSecondN02701MinusPointP018RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP018Factor2576
        sharedSecondN02701MinusPointP018Center2576) =
        sharedSecondN02701MinusPointP018Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP018RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP018Rounded2576‖ ≤
          sharedSecondN02701MinusPointP018Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP018Factor2576
      sharedSecondN02701MinusPointP018Center2576)
  rw [sharedSecondN02701MinusPointP018RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP018Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP018Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP018Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP018DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP018Factor2576,
      sharedSecondN02701MinusPointP018Error2576, rounding2542,
      sharedSecondN02701MinusPointP018Radius2576]

theorem sharedSecondN02701MinusPointP018DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP018Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP018RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP018Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP018Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP018Rounded2576]

def sharedSecondN02701MinusPointP019Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP019Radius2576 : ℝ := ((2200557396131 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02701MinusPointP019RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP019Factor2576
        sharedSecondN02701MinusPointP019Center2576) =
        sharedSecondN02701MinusPointP019Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP019RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP019Rounded2576‖ ≤
          sharedSecondN02701MinusPointP019Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP019Factor2576
      sharedSecondN02701MinusPointP019Center2576)
  rw [sharedSecondN02701MinusPointP019RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP019Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP019Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP019Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP019DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP019Factor2576,
      sharedSecondN02701MinusPointP019Error2576, rounding2542,
      sharedSecondN02701MinusPointP019Radius2576]

theorem sharedSecondN02701MinusPointP019DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP019Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP019RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP019Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP019Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP019Rounded2576]

def sharedSecondN02701MinusPointP020Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP020Radius2576 : ℝ := ((2200557396507 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02701MinusPointP020RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP020Factor2576
        sharedSecondN02701MinusPointP020Center2576) =
        sharedSecondN02701MinusPointP020Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP020RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP020Rounded2576‖ ≤
          sharedSecondN02701MinusPointP020Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP020Factor2576
      sharedSecondN02701MinusPointP020Center2576)
  rw [sharedSecondN02701MinusPointP020RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP020Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP020Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP020Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP020DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP020Factor2576,
      sharedSecondN02701MinusPointP020Error2576, rounding2542,
      sharedSecondN02701MinusPointP020Radius2576]

theorem sharedSecondN02701MinusPointP020DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP020Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP020RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP020Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP020Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP020Rounded2576]

def sharedSecondN02701MinusPointP021Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP021Radius2576 : ℝ := ((2200557396821 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02701MinusPointP021RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP021Factor2576
        sharedSecondN02701MinusPointP021Center2576) =
        sharedSecondN02701MinusPointP021Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP021RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP021Rounded2576‖ ≤
          sharedSecondN02701MinusPointP021Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP021Factor2576
      sharedSecondN02701MinusPointP021Center2576)
  rw [sharedSecondN02701MinusPointP021RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP021Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP021Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP021Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP021DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP021Factor2576,
      sharedSecondN02701MinusPointP021Error2576, rounding2542,
      sharedSecondN02701MinusPointP021Radius2576]

theorem sharedSecondN02701MinusPointP021DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP021Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP021RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP021Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP021Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP021Rounded2576]

def sharedSecondN02701MinusPointP022Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP022Radius2576 : ℝ := ((1100278698491 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem sharedSecondN02701MinusPointP022RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP022Factor2576
        sharedSecondN02701MinusPointP022Center2576) =
        sharedSecondN02701MinusPointP022Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP022RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP022Rounded2576‖ ≤
          sharedSecondN02701MinusPointP022Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP022Factor2576
      sharedSecondN02701MinusPointP022Center2576)
  rw [sharedSecondN02701MinusPointP022RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP022Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP022Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP022Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP022DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP022Factor2576,
      sharedSecondN02701MinusPointP022Error2576, rounding2542,
      sharedSecondN02701MinusPointP022Radius2576]

theorem sharedSecondN02701MinusPointP022DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP022Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP022RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP022Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP022Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP022Rounded2576]

def sharedSecondN02701MinusPointP023Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP023Radius2576 : ℝ := ((2200557397445 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02701MinusPointP023RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP023Factor2576
        sharedSecondN02701MinusPointP023Center2576) =
        sharedSecondN02701MinusPointP023Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP023RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP023Rounded2576‖ ≤
          sharedSecondN02701MinusPointP023Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP023Factor2576
      sharedSecondN02701MinusPointP023Center2576)
  rw [sharedSecondN02701MinusPointP023RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP023Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP023Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP023Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP023DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP023Factor2576,
      sharedSecondN02701MinusPointP023Error2576, rounding2542,
      sharedSecondN02701MinusPointP023Radius2576]

theorem sharedSecondN02701MinusPointP023DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP023Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP023RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP023Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP023Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP023Rounded2576]

def sharedSecondN02701MinusPointP024Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP024Radius2576 : ℝ := ((1100278698829 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem sharedSecondN02701MinusPointP024RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP024Factor2576
        sharedSecondN02701MinusPointP024Center2576) =
        sharedSecondN02701MinusPointP024Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP024RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP024Rounded2576‖ ≤
          sharedSecondN02701MinusPointP024Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP024Factor2576
      sharedSecondN02701MinusPointP024Center2576)
  rw [sharedSecondN02701MinusPointP024RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP024Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP024Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP024Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP024DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP024Factor2576,
      sharedSecondN02701MinusPointP024Error2576, rounding2542,
      sharedSecondN02701MinusPointP024Radius2576]

theorem sharedSecondN02701MinusPointP024DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP024Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP024RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP024Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP024Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP024Rounded2576]

def sharedSecondN02701MinusPointP025Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP025Radius2576 : ℝ := ((2200557397925 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02701MinusPointP025RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP025Factor2576
        sharedSecondN02701MinusPointP025Center2576) =
        sharedSecondN02701MinusPointP025Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP025RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP025Rounded2576‖ ≤
          sharedSecondN02701MinusPointP025Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP025Factor2576
      sharedSecondN02701MinusPointP025Center2576)
  rw [sharedSecondN02701MinusPointP025RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP025Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP025Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP025Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP025DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP025Factor2576,
      sharedSecondN02701MinusPointP025Error2576, rounding2542,
      sharedSecondN02701MinusPointP025Radius2576]

theorem sharedSecondN02701MinusPointP025DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP025Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP025RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP025Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP025Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP025Rounded2576]

def sharedSecondN02701MinusPointP026Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP026Radius2576 : ℝ := ((2200557398197 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02701MinusPointP026RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP026Factor2576
        sharedSecondN02701MinusPointP026Center2576) =
        sharedSecondN02701MinusPointP026Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP026RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP026Rounded2576‖ ≤
          sharedSecondN02701MinusPointP026Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP026Factor2576
      sharedSecondN02701MinusPointP026Center2576)
  rw [sharedSecondN02701MinusPointP026RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP026Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP026Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP026Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP026DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP026Factor2576,
      sharedSecondN02701MinusPointP026Error2576, rounding2542,
      sharedSecondN02701MinusPointP026Radius2576]

theorem sharedSecondN02701MinusPointP026DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP026Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP026RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP026Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP026Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP026Rounded2576]

def sharedSecondN02701MinusPointP027Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP027Radius2576 : ℝ := ((2200557398591 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02701MinusPointP027RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP027Factor2576
        sharedSecondN02701MinusPointP027Center2576) =
        sharedSecondN02701MinusPointP027Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP027RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP027Rounded2576‖ ≤
          sharedSecondN02701MinusPointP027Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP027Factor2576
      sharedSecondN02701MinusPointP027Center2576)
  rw [sharedSecondN02701MinusPointP027RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP027Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP027Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP027Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP027DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP027Factor2576,
      sharedSecondN02701MinusPointP027Error2576, rounding2542,
      sharedSecondN02701MinusPointP027Radius2576]

theorem sharedSecondN02701MinusPointP027DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP027Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP027RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP027Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP027Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP027Rounded2576]

def sharedSecondN02701MinusPointP028Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP028Radius2576 : ℝ := ((2200557398747 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02701MinusPointP028RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP028Factor2576
        sharedSecondN02701MinusPointP028Center2576) =
        sharedSecondN02701MinusPointP028Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP028RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP028Rounded2576‖ ≤
          sharedSecondN02701MinusPointP028Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP028Factor2576
      sharedSecondN02701MinusPointP028Center2576)
  rw [sharedSecondN02701MinusPointP028RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP028Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP028Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP028Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP028DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP028Factor2576,
      sharedSecondN02701MinusPointP028Error2576, rounding2542,
      sharedSecondN02701MinusPointP028Radius2576]

theorem sharedSecondN02701MinusPointP028DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP028Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP028RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP028Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP028Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP028Rounded2576]

def sharedSecondN02701MinusPointP029Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02701MinusPointP029Radius2576 : ℝ := ((275069674873 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem sharedSecondN02701MinusPointP029RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02701MinusPointP029Factor2576
        sharedSecondN02701MinusPointP029Center2576) =
        sharedSecondN02701MinusPointP029Rounded2576 := by
  cbv

theorem sharedSecondN02701MinusPointP029RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02701MinusPointPosition2576 -
      embedPair2542 sharedSecondN02701MinusPointP029Rounded2576‖ ≤
          sharedSecondN02701MinusPointP029Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02701MinusPointP029Factor2576
      sharedSecondN02701MinusPointP029Center2576)
  rw [sharedSecondN02701MinusPointP029RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP029Factor2576 * embedPair2542
        sharedSecondN02701MinusPointP029Center2576)
    (embedPair2542 sharedSecondN02701MinusPointP029Rounded2576)).trans (add_le_add
        sharedSecondN02701MinusPointP029DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02701MinusPointP029Factor2576,
      sharedSecondN02701MinusPointP029Error2576, rounding2542,
      sharedSecondN02701MinusPointP029Radius2576]

theorem sharedSecondN02701MinusPointP029DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02701MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02701MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02701MinusPointPosition2576)
    (embedPair2542 sharedSecondN02701MinusPointP029Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02701MinusPointP029RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02701MinusPointP029Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02701MinusPointP029Radius2576, pairMagnitude2542,
      sharedSecondN02701MinusPointP029Rounded2576]

noncomputable def sharedSecondN02701MinusSignedValue2576 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 sharedSecondN02701MinusPointP000Rounded2576
  | 1 => embedPair2542 sharedSecondN02701MinusPointP001Rounded2576
  | 2 => embedPair2542 sharedSecondN02701MinusPointP002Rounded2576
  | 3 => embedPair2542 sharedSecondN02701MinusPointP003Rounded2576
  | 4 => embedPair2542 sharedSecondN02701MinusPointP004Rounded2576
  | 5 => embedPair2542 sharedSecondN02701MinusPointP005Rounded2576
  | 6 => embedPair2542 sharedSecondN02701MinusPointP006Rounded2576
  | 7 => embedPair2542 sharedSecondN02701MinusPointP007Rounded2576
  | 8 => embedPair2542 sharedSecondN02701MinusPointP008Rounded2576
  | 9 => embedPair2542 sharedSecondN02701MinusPointP009Rounded2576
  | 10 => embedPair2542 sharedSecondN02701MinusPointP010Rounded2576
  | 11 => embedPair2542 sharedSecondN02701MinusPointP011Rounded2576
  | 12 => embedPair2542 sharedSecondN02701MinusPointP012Rounded2576
  | 13 => embedPair2542 sharedSecondN02701MinusPointP013Rounded2576
  | 14 => embedPair2542 sharedSecondN02701MinusPointP014Rounded2576
  | 15 => embedPair2542 sharedSecondN02701MinusPointP015Rounded2576
  | 16 => embedPair2542 sharedSecondN02701MinusPointP016Rounded2576
  | 17 => embedPair2542 sharedSecondN02701MinusPointP017Rounded2576
  | 18 => embedPair2542 sharedSecondN02701MinusPointP018Rounded2576
  | 19 => embedPair2542 sharedSecondN02701MinusPointP019Rounded2576
  | 20 => embedPair2542 sharedSecondN02701MinusPointP020Rounded2576
  | 21 => embedPair2542 sharedSecondN02701MinusPointP021Rounded2576
  | 22 => embedPair2542 sharedSecondN02701MinusPointP022Rounded2576
  | 23 => embedPair2542 sharedSecondN02701MinusPointP023Rounded2576
  | 24 => embedPair2542 sharedSecondN02701MinusPointP024Rounded2576
  | 25 => embedPair2542 sharedSecondN02701MinusPointP025Rounded2576
  | 26 => embedPair2542 sharedSecondN02701MinusPointP026Rounded2576
  | 27 => embedPair2542 sharedSecondN02701MinusPointP027Rounded2576
  | 28 => embedPair2542 sharedSecondN02701MinusPointP028Rounded2576
  | 29 => embedPair2542 sharedSecondN02701MinusPointP029Rounded2576
  | _ => 0

noncomputable def sharedSecondN02701MinusSignedError2576 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => sharedSecondN02701MinusPointP000Radius2576
  | 1 => sharedSecondN02701MinusPointP001Radius2576
  | 2 => sharedSecondN02701MinusPointP002Radius2576
  | 3 => sharedSecondN02701MinusPointP003Radius2576
  | 4 => sharedSecondN02701MinusPointP004Radius2576
  | 5 => sharedSecondN02701MinusPointP005Radius2576
  | 6 => sharedSecondN02701MinusPointP006Radius2576
  | 7 => sharedSecondN02701MinusPointP007Radius2576
  | 8 => sharedSecondN02701MinusPointP008Radius2576
  | 9 => sharedSecondN02701MinusPointP009Radius2576
  | 10 => sharedSecondN02701MinusPointP010Radius2576
  | 11 => sharedSecondN02701MinusPointP011Radius2576
  | 12 => sharedSecondN02701MinusPointP012Radius2576
  | 13 => sharedSecondN02701MinusPointP013Radius2576
  | 14 => sharedSecondN02701MinusPointP014Radius2576
  | 15 => sharedSecondN02701MinusPointP015Radius2576
  | 16 => sharedSecondN02701MinusPointP016Radius2576
  | 17 => sharedSecondN02701MinusPointP017Radius2576
  | 18 => sharedSecondN02701MinusPointP018Radius2576
  | 19 => sharedSecondN02701MinusPointP019Radius2576
  | 20 => sharedSecondN02701MinusPointP020Radius2576
  | 21 => sharedSecondN02701MinusPointP021Radius2576
  | 22 => sharedSecondN02701MinusPointP022Radius2576
  | 23 => sharedSecondN02701MinusPointP023Radius2576
  | 24 => sharedSecondN02701MinusPointP024Radius2576
  | 25 => sharedSecondN02701MinusPointP025Radius2576
  | 26 => sharedSecondN02701MinusPointP026Radius2576
  | 27 => sharedSecondN02701MinusPointP027Radius2576
  | 28 => sharedSecondN02701MinusPointP028Radius2576
  | 29 => sharedSecondN02701MinusPointP029Radius2576
  | _ => 0

theorem sharedSecondN02701MinusSignedExpError2576 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i sharedSecondN02701MinusPointPosition2576 -
        sharedSecondN02701MinusSignedValue2576 i‖ ≤ sharedSecondN02701MinusSignedError2576 i := by
  fin_cases i
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP000RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP001RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP002RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP003RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP004RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP005RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP006RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP007RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP008RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP009RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP010RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP011RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP012RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP013RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP014RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP015RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP016RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP017RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP018RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP019RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP020RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP021RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP022RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP023RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP024RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP025RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP026RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP027RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP028RoundedError2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP029RoundedError2576

theorem sharedSecondN02701MinusSignedUnitNorm2576 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i sharedSecondN02701MinusPointPosition2576‖ ≤
        1
        := by
  fin_cases i
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP000DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP001DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP002DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP003DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP004DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP005DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP006DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP007DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP008DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP009DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP010DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP011DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP012DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP013DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP014DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP015DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP016DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP017DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP018DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP019DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP020DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP021DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP022DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP023DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP024DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP025DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP026DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP027DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP028DerivativeNorm2576
  · simpa only [sharedSecondN02701MinusSignedValue2576, sharedSecondN02701MinusSignedError2576]
      using
      sharedSecondN02701MinusPointP029DerivativeNorm2576

noncomputable def sharedSecondN02701MinusSignedSum2576 : ℂ := ⟨(((-(((8116033180039 * 10^40
        + 9110529979434127744120159328934572290595) * 10^40
        + 2422199595343076930443488471728200789525) * 10^40
        + 952128579427651536757456050609430856769)) : ℝ) /
        (((354901720847 * 10^40
        + 4643020260370155703147140398639456481045) * 10^40
        + 2162182138631867152739912007974911672398) * 10^40
        + 1329865996466075003059657194108692201472)),
    (((((12769081039942 * 10^40
        + 8253537185054847441066881503690904794106) * 10^40
        + 3257107199207252017835938150418780934693) * 10^40
        + 5994326974048193880873186866832571784011) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888))⟩

noncomputable def sharedSecondN02701MinusSignedUpper2576 : ℝ := ((1228688317 : ℝ) /
        50000000)

theorem sharedSecondN02701MinusSignedSum_eq2576 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * sharedSecondN02701MinusSignedValue2576 i) =
      sharedSecondN02701MinusSignedSum2576 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        sharedSecondN02701MinusSignedValue2576,
      sharedSecondN02701MinusSignedSum2576, embedPair2542,
          sharedSecondN02701MinusPointP000Rounded2576,
      sharedSecondN02701MinusPointP001Rounded2576,
      sharedSecondN02701MinusPointP002Rounded2576,
      sharedSecondN02701MinusPointP003Rounded2576,
      sharedSecondN02701MinusPointP004Rounded2576,
      sharedSecondN02701MinusPointP005Rounded2576,
      sharedSecondN02701MinusPointP006Rounded2576,
      sharedSecondN02701MinusPointP007Rounded2576,
      sharedSecondN02701MinusPointP008Rounded2576,
      sharedSecondN02701MinusPointP009Rounded2576,
      sharedSecondN02701MinusPointP010Rounded2576,
      sharedSecondN02701MinusPointP011Rounded2576,
      sharedSecondN02701MinusPointP012Rounded2576,
      sharedSecondN02701MinusPointP013Rounded2576,
      sharedSecondN02701MinusPointP014Rounded2576,
      sharedSecondN02701MinusPointP015Rounded2576,
      sharedSecondN02701MinusPointP016Rounded2576,
      sharedSecondN02701MinusPointP017Rounded2576,
      sharedSecondN02701MinusPointP018Rounded2576,
      sharedSecondN02701MinusPointP019Rounded2576,
      sharedSecondN02701MinusPointP020Rounded2576,
      sharedSecondN02701MinusPointP021Rounded2576,
      sharedSecondN02701MinusPointP022Rounded2576,
      sharedSecondN02701MinusPointP023Rounded2576,
      sharedSecondN02701MinusPointP024Rounded2576,
      sharedSecondN02701MinusPointP025Rounded2576,
      sharedSecondN02701MinusPointP026Rounded2576,
      sharedSecondN02701MinusPointP027Rounded2576,
      sharedSecondN02701MinusPointP028Rounded2576,
      sharedSecondN02701MinusPointP029Rounded2576, Complex.mul_re, Complex.mul_im]

theorem sharedSecondN02701MinusSignedSum_norm2576 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * sharedSecondN02701MinusSignedValue2576 i‖ ≤
        ((153586039 :
        ℝ) /
        6250000) := by
  rw [sharedSecondN02701MinusSignedSum_eq2576]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [sharedSecondN02701MinusSignedSum2576]

theorem sharedSecondN02701MinusSignedCharge2576 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * sharedSecondN02701MinusSignedError2576 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      sharedSecondN02701MinusSignedError2576, sharedSecondN02701MinusPointP000Radius2576,
      sharedSecondN02701MinusPointP001Radius2576,
      sharedSecondN02701MinusPointP002Radius2576,
      sharedSecondN02701MinusPointP003Radius2576,
      sharedSecondN02701MinusPointP004Radius2576,
      sharedSecondN02701MinusPointP005Radius2576,
      sharedSecondN02701MinusPointP006Radius2576,
      sharedSecondN02701MinusPointP007Radius2576,
      sharedSecondN02701MinusPointP008Radius2576,
      sharedSecondN02701MinusPointP009Radius2576,
      sharedSecondN02701MinusPointP010Radius2576,
      sharedSecondN02701MinusPointP011Radius2576,
      sharedSecondN02701MinusPointP012Radius2576,
      sharedSecondN02701MinusPointP013Radius2576,
      sharedSecondN02701MinusPointP014Radius2576,
      sharedSecondN02701MinusPointP015Radius2576,
      sharedSecondN02701MinusPointP016Radius2576,
      sharedSecondN02701MinusPointP017Radius2576,
      sharedSecondN02701MinusPointP018Radius2576,
      sharedSecondN02701MinusPointP019Radius2576,
      sharedSecondN02701MinusPointP020Radius2576,
      sharedSecondN02701MinusPointP021Radius2576,
      sharedSecondN02701MinusPointP022Radius2576,
      sharedSecondN02701MinusPointP023Radius2576,
      sharedSecondN02701MinusPointP024Radius2576,
      sharedSecondN02701MinusPointP025Radius2576,
      sharedSecondN02701MinusPointP026Radius2576,
      sharedSecondN02701MinusPointP027Radius2576,
      sharedSecondN02701MinusPointP028Radius2576,
      sharedSecondN02701MinusPointP029Radius2576]

theorem sharedSecondN02701MinusSignedUpper_le2576 :
    signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 sharedSecondN02701MinusPointPosition2576 ≤
          sharedSecondN02701MinusSignedUpper2576 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i
            sharedSecondN02701MinusPointPosition2576‖
            ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * sharedSecondN02701MinusSignedValue2576 i‖
          +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * sharedSecondN02701MinusSignedError2576 i :=
              by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (sharedSecondN02701MinusSignedExpError2576 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i sharedSecondN02701MinusPointPosition2576‖
          ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (sharedSecondN02701MinusSignedUnitNorm2576 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i
          sharedSecondN02701MinusPointPosition2576‖)
          ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 sharedSecondN02701MinusSignedUpper2576
  linarith [sharedSecondN02701MinusSignedSum_norm2576, sharedSecondN02701MinusSignedCharge2576]

theorem sharedSecondN02701MinusPhysical2576 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        sharedSecondN02701MinusPointPosition2576‖ ≤
      sharedSecondN02701MinusSignedUpper2576 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        sharedSecondN02701MinusPointPosition2576
  exact h.trans sharedSecondN02701MinusSignedUpper_le2576

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.sharedSecondN02701MinusSignedExpError2576
#print axioms ConnesWeilRH.Dev.sharedSecondN02701MinusSignedSum_eq2576
#print axioms ConnesWeilRH.Dev.sharedSecondN02701MinusSignedCharge2576
#print axioms ConnesWeilRH.Dev.sharedSecondN02701MinusSignedUpper_le2576
#print axioms ConnesWeilRH.Dev.sharedSecondN02701MinusPhysical2576
