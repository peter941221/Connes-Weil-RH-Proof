import ConnesWeilRH.Dev.C1RouteASharedSecondN02700MinusDerivatives2576
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem sharedSecondN02700MinusPoint_triangle2576 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def sharedSecondN02700MinusPointP000Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP000Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP000RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP000Factor2576
        sharedSecondN02700MinusPointP000Center2576) =
        sharedSecondN02700MinusPointP000Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP000RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP000Rounded2576‖ ≤
          sharedSecondN02700MinusPointP000Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP000Factor2576
      sharedSecondN02700MinusPointP000Center2576)
  rw [sharedSecondN02700MinusPointP000RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP000Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP000Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP000Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP000DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP000Factor2576,
      sharedSecondN02700MinusPointP000Error2576, rounding2542,
      sharedSecondN02700MinusPointP000Radius2576]

theorem sharedSecondN02700MinusPointP000DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP000Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP000RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP000Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP000Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP000Rounded2576]

def sharedSecondN02700MinusPointP001Rounded2576 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP001Radius2576 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02700MinusPointP001RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP001Factor2576
        sharedSecondN02700MinusPointP001Center2576) =
        sharedSecondN02700MinusPointP001Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP001RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP001Rounded2576‖ ≤
          sharedSecondN02700MinusPointP001Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP001Factor2576
      sharedSecondN02700MinusPointP001Center2576)
  rw [sharedSecondN02700MinusPointP001RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP001Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP001Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP001Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP001DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP001Factor2576,
      sharedSecondN02700MinusPointP001Error2576, rounding2542,
      sharedSecondN02700MinusPointP001Radius2576]

theorem sharedSecondN02700MinusPointP001DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP001Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP001RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP001Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP001Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP001Rounded2576]

def sharedSecondN02700MinusPointP002Rounded2576 : RatPair2542 :=
  (((28161701 : ℚ) /
        1267650600228229401496703205376),
    (((-11070949) : ℚ) /
        633825300114114700748351602688))

noncomputable def sharedSecondN02700MinusPointP002Radius2576 : ℝ := ((2199023390103 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02700MinusPointP002RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP002Factor2576
        sharedSecondN02700MinusPointP002Center2576) =
        sharedSecondN02700MinusPointP002Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP002RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP002Rounded2576‖ ≤
          sharedSecondN02700MinusPointP002Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP002Factor2576
      sharedSecondN02700MinusPointP002Center2576)
  rw [sharedSecondN02700MinusPointP002RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP002Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP002Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP002Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP002DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP002Factor2576,
      sharedSecondN02700MinusPointP002Error2576, rounding2542,
      sharedSecondN02700MinusPointP002Radius2576]

theorem sharedSecondN02700MinusPointP002DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP002Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP002RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP002Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP002Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP002Rounded2576]

def sharedSecondN02700MinusPointP003Rounded2576 : RatPair2542 :=
  (((82964876946047 : ℚ) /
        316912650057057350374175801344),
    ((5530890319949 : ℚ) /
        79228162514264337593543950336))

noncomputable def sharedSecondN02700MinusPointP003Radius2576 : ℝ := ((962463443223 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem sharedSecondN02700MinusPointP003RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP003Factor2576
        sharedSecondN02700MinusPointP003Center2576) =
        sharedSecondN02700MinusPointP003Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP003RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP003Rounded2576‖ ≤
          sharedSecondN02700MinusPointP003Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP003Factor2576
      sharedSecondN02700MinusPointP003Center2576)
  rw [sharedSecondN02700MinusPointP003RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP003Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP003Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP003Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP003DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP003Factor2576,
      sharedSecondN02700MinusPointP003Error2576, rounding2542,
      sharedSecondN02700MinusPointP003Radius2576]

theorem sharedSecondN02700MinusPointP003DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP003Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP003RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP003Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP003Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP003Rounded2576]

def sharedSecondN02700MinusPointP004Rounded2576 : RatPair2542 :=
  (((32763306632307601 : ℚ) /
        316912650057057350374175801344),
    (((-89250173431151475) : ℚ) /
        1267650600228229401496703205376))

noncomputable def sharedSecondN02700MinusPointP004Radius2576 : ℝ := ((676340962967073 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02700MinusPointP004RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP004Factor2576
        sharedSecondN02700MinusPointP004Center2576) =
        sharedSecondN02700MinusPointP004Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP004RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP004Rounded2576‖ ≤
          sharedSecondN02700MinusPointP004Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP004Factor2576
      sharedSecondN02700MinusPointP004Center2576)
  rw [sharedSecondN02700MinusPointP004RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP004Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP004Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP004Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP004DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP004Factor2576,
      sharedSecondN02700MinusPointP004Error2576, rounding2542,
      sharedSecondN02700MinusPointP004Radius2576]

theorem sharedSecondN02700MinusPointP004DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP004Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP004RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP004Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP004Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP004Rounded2576]

def sharedSecondN02700MinusPointP005Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP005Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP005RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP005Factor2576
        sharedSecondN02700MinusPointP005Center2576) =
        sharedSecondN02700MinusPointP005Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP005RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP005Rounded2576‖ ≤
          sharedSecondN02700MinusPointP005Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP005Factor2576
      sharedSecondN02700MinusPointP005Center2576)
  rw [sharedSecondN02700MinusPointP005RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP005Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP005Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP005Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP005DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP005Factor2576,
      sharedSecondN02700MinusPointP005Error2576, rounding2542,
      sharedSecondN02700MinusPointP005Radius2576]

theorem sharedSecondN02700MinusPointP005DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP005Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP005RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP005Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP005Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP005Rounded2576]

def sharedSecondN02700MinusPointP006Rounded2576 : RatPair2542 :=
  (((21 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP006Radius2576 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02700MinusPointP006RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP006Factor2576
        sharedSecondN02700MinusPointP006Center2576) =
        sharedSecondN02700MinusPointP006Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP006RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP006Rounded2576‖ ≤
          sharedSecondN02700MinusPointP006Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP006Factor2576
      sharedSecondN02700MinusPointP006Center2576)
  rw [sharedSecondN02700MinusPointP006RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP006Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP006Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP006Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP006DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP006Factor2576,
      sharedSecondN02700MinusPointP006Error2576, rounding2542,
      sharedSecondN02700MinusPointP006Radius2576]

theorem sharedSecondN02700MinusPointP006DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP006Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP006RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP006Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP006Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP006Rounded2576]

def sharedSecondN02700MinusPointP007Rounded2576 : RatPair2542 :=
  (((17518673253473 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP007Radius2576 : ℝ := ((2203873831015 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02700MinusPointP007RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP007Factor2576
        sharedSecondN02700MinusPointP007Center2576) =
        sharedSecondN02700MinusPointP007Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP007RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP007Rounded2576‖ ≤
          sharedSecondN02700MinusPointP007Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP007Factor2576
      sharedSecondN02700MinusPointP007Center2576)
  rw [sharedSecondN02700MinusPointP007RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP007Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP007Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP007Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP007DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP007Factor2576,
      sharedSecondN02700MinusPointP007Error2576, rounding2542,
      sharedSecondN02700MinusPointP007Radius2576]

theorem sharedSecondN02700MinusPointP007DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP007Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP007RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP007Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP007Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP007Rounded2576]

def sharedSecondN02700MinusPointP008Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP008Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP008RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP008Factor2576
        sharedSecondN02700MinusPointP008Center2576) =
        sharedSecondN02700MinusPointP008Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP008RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP008Rounded2576‖ ≤
          sharedSecondN02700MinusPointP008Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP008Factor2576
      sharedSecondN02700MinusPointP008Center2576)
  rw [sharedSecondN02700MinusPointP008RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP008Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP008Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP008Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP008DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP008Factor2576,
      sharedSecondN02700MinusPointP008Error2576, rounding2542,
      sharedSecondN02700MinusPointP008Radius2576]

theorem sharedSecondN02700MinusPointP008DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP008Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP008RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP008Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP008Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP008Rounded2576]

def sharedSecondN02700MinusPointP009Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP009Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP009RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP009Factor2576
        sharedSecondN02700MinusPointP009Center2576) =
        sharedSecondN02700MinusPointP009Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP009RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP009Rounded2576‖ ≤
          sharedSecondN02700MinusPointP009Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP009Factor2576
      sharedSecondN02700MinusPointP009Center2576)
  rw [sharedSecondN02700MinusPointP009RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP009Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP009Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP009Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP009DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP009Factor2576,
      sharedSecondN02700MinusPointP009Error2576, rounding2542,
      sharedSecondN02700MinusPointP009Radius2576]

theorem sharedSecondN02700MinusPointP009DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP009Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP009RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP009Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP009Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP009Rounded2576]

def sharedSecondN02700MinusPointP010Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP010Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP010RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP010Factor2576
        sharedSecondN02700MinusPointP010Center2576) =
        sharedSecondN02700MinusPointP010Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP010RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP010Rounded2576‖ ≤
          sharedSecondN02700MinusPointP010Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP010Factor2576
      sharedSecondN02700MinusPointP010Center2576)
  rw [sharedSecondN02700MinusPointP010RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP010Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP010Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP010Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP010DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP010Factor2576,
      sharedSecondN02700MinusPointP010Error2576, rounding2542,
      sharedSecondN02700MinusPointP010Radius2576]

theorem sharedSecondN02700MinusPointP010DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP010Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP010RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP010Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP010Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP010Rounded2576]

def sharedSecondN02700MinusPointP011Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP011Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP011RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP011Factor2576
        sharedSecondN02700MinusPointP011Center2576) =
        sharedSecondN02700MinusPointP011Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP011RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP011Rounded2576‖ ≤
          sharedSecondN02700MinusPointP011Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP011Factor2576
      sharedSecondN02700MinusPointP011Center2576)
  rw [sharedSecondN02700MinusPointP011RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP011Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP011Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP011Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP011DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP011Factor2576,
      sharedSecondN02700MinusPointP011Error2576, rounding2542,
      sharedSecondN02700MinusPointP011Radius2576]

theorem sharedSecondN02700MinusPointP011DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP011Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP011RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP011Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP011Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP011Rounded2576]

def sharedSecondN02700MinusPointP012Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP012Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP012RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP012Factor2576
        sharedSecondN02700MinusPointP012Center2576) =
        sharedSecondN02700MinusPointP012Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP012RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP012Rounded2576‖ ≤
          sharedSecondN02700MinusPointP012Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP012Factor2576
      sharedSecondN02700MinusPointP012Center2576)
  rw [sharedSecondN02700MinusPointP012RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP012Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP012Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP012Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP012DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP012Factor2576,
      sharedSecondN02700MinusPointP012Error2576, rounding2542,
      sharedSecondN02700MinusPointP012Radius2576]

theorem sharedSecondN02700MinusPointP012DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP012Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP012RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP012Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP012Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP012Rounded2576]

def sharedSecondN02700MinusPointP013Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP013Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP013RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP013Factor2576
        sharedSecondN02700MinusPointP013Center2576) =
        sharedSecondN02700MinusPointP013Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP013RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP013Rounded2576‖ ≤
          sharedSecondN02700MinusPointP013Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP013Factor2576
      sharedSecondN02700MinusPointP013Center2576)
  rw [sharedSecondN02700MinusPointP013RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP013Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP013Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP013Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP013DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP013Factor2576,
      sharedSecondN02700MinusPointP013Error2576, rounding2542,
      sharedSecondN02700MinusPointP013Radius2576]

theorem sharedSecondN02700MinusPointP013DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP013Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP013RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP013Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP013Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP013Rounded2576]

def sharedSecondN02700MinusPointP014Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP014Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP014RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP014Factor2576
        sharedSecondN02700MinusPointP014Center2576) =
        sharedSecondN02700MinusPointP014Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP014RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP014Rounded2576‖ ≤
          sharedSecondN02700MinusPointP014Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP014Factor2576
      sharedSecondN02700MinusPointP014Center2576)
  rw [sharedSecondN02700MinusPointP014RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP014Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP014Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP014Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP014DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP014Factor2576,
      sharedSecondN02700MinusPointP014Error2576, rounding2542,
      sharedSecondN02700MinusPointP014Radius2576]

theorem sharedSecondN02700MinusPointP014DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP014Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP014RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP014Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP014Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP014Rounded2576]

def sharedSecondN02700MinusPointP015Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP015Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP015RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP015Factor2576
        sharedSecondN02700MinusPointP015Center2576) =
        sharedSecondN02700MinusPointP015Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP015RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP015Rounded2576‖ ≤
          sharedSecondN02700MinusPointP015Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP015Factor2576
      sharedSecondN02700MinusPointP015Center2576)
  rw [sharedSecondN02700MinusPointP015RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP015Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP015Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP015Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP015DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP015Factor2576,
      sharedSecondN02700MinusPointP015Error2576, rounding2542,
      sharedSecondN02700MinusPointP015Radius2576]

theorem sharedSecondN02700MinusPointP015DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP015Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP015RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP015Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP015Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP015Rounded2576]

def sharedSecondN02700MinusPointP016Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP016Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP016RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP016Factor2576
        sharedSecondN02700MinusPointP016Center2576) =
        sharedSecondN02700MinusPointP016Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP016RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP016Rounded2576‖ ≤
          sharedSecondN02700MinusPointP016Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP016Factor2576
      sharedSecondN02700MinusPointP016Center2576)
  rw [sharedSecondN02700MinusPointP016RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP016Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP016Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP016Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP016DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP016Factor2576,
      sharedSecondN02700MinusPointP016Error2576, rounding2542,
      sharedSecondN02700MinusPointP016Radius2576]

theorem sharedSecondN02700MinusPointP016DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP016Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP016RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP016Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP016Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP016Rounded2576]

def sharedSecondN02700MinusPointP017Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP017Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP017RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP017Factor2576
        sharedSecondN02700MinusPointP017Center2576) =
        sharedSecondN02700MinusPointP017Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP017RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP017Rounded2576‖ ≤
          sharedSecondN02700MinusPointP017Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP017Factor2576
      sharedSecondN02700MinusPointP017Center2576)
  rw [sharedSecondN02700MinusPointP017RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP017Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP017Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP017Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP017DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP017Factor2576,
      sharedSecondN02700MinusPointP017Error2576, rounding2542,
      sharedSecondN02700MinusPointP017Radius2576]

theorem sharedSecondN02700MinusPointP017DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP017Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP017RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP017Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP017Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP017Rounded2576]

def sharedSecondN02700MinusPointP018Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP018Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP018RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP018Factor2576
        sharedSecondN02700MinusPointP018Center2576) =
        sharedSecondN02700MinusPointP018Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP018RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP018Rounded2576‖ ≤
          sharedSecondN02700MinusPointP018Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP018Factor2576
      sharedSecondN02700MinusPointP018Center2576)
  rw [sharedSecondN02700MinusPointP018RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP018Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP018Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP018Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP018DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP018Factor2576,
      sharedSecondN02700MinusPointP018Error2576, rounding2542,
      sharedSecondN02700MinusPointP018Radius2576]

theorem sharedSecondN02700MinusPointP018DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP018Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP018RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP018Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP018Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP018Rounded2576]

def sharedSecondN02700MinusPointP019Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP019Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP019RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP019Factor2576
        sharedSecondN02700MinusPointP019Center2576) =
        sharedSecondN02700MinusPointP019Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP019RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP019Rounded2576‖ ≤
          sharedSecondN02700MinusPointP019Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP019Factor2576
      sharedSecondN02700MinusPointP019Center2576)
  rw [sharedSecondN02700MinusPointP019RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP019Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP019Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP019Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP019DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP019Factor2576,
      sharedSecondN02700MinusPointP019Error2576, rounding2542,
      sharedSecondN02700MinusPointP019Radius2576]

theorem sharedSecondN02700MinusPointP019DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP019Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP019RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP019Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP019Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP019Rounded2576]

def sharedSecondN02700MinusPointP020Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP020Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP020RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP020Factor2576
        sharedSecondN02700MinusPointP020Center2576) =
        sharedSecondN02700MinusPointP020Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP020RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP020Rounded2576‖ ≤
          sharedSecondN02700MinusPointP020Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP020Factor2576
      sharedSecondN02700MinusPointP020Center2576)
  rw [sharedSecondN02700MinusPointP020RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP020Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP020Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP020Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP020DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP020Factor2576,
      sharedSecondN02700MinusPointP020Error2576, rounding2542,
      sharedSecondN02700MinusPointP020Radius2576]

theorem sharedSecondN02700MinusPointP020DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP020Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP020RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP020Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP020Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP020Rounded2576]

def sharedSecondN02700MinusPointP021Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP021Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP021RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP021Factor2576
        sharedSecondN02700MinusPointP021Center2576) =
        sharedSecondN02700MinusPointP021Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP021RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP021Rounded2576‖ ≤
          sharedSecondN02700MinusPointP021Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP021Factor2576
      sharedSecondN02700MinusPointP021Center2576)
  rw [sharedSecondN02700MinusPointP021RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP021Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP021Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP021Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP021DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP021Factor2576,
      sharedSecondN02700MinusPointP021Error2576, rounding2542,
      sharedSecondN02700MinusPointP021Radius2576]

theorem sharedSecondN02700MinusPointP021DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP021Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP021RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP021Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP021Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP021Rounded2576]

def sharedSecondN02700MinusPointP022Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP022Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP022RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP022Factor2576
        sharedSecondN02700MinusPointP022Center2576) =
        sharedSecondN02700MinusPointP022Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP022RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP022Rounded2576‖ ≤
          sharedSecondN02700MinusPointP022Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP022Factor2576
      sharedSecondN02700MinusPointP022Center2576)
  rw [sharedSecondN02700MinusPointP022RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP022Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP022Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP022Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP022DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP022Factor2576,
      sharedSecondN02700MinusPointP022Error2576, rounding2542,
      sharedSecondN02700MinusPointP022Radius2576]

theorem sharedSecondN02700MinusPointP022DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP022Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP022RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP022Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP022Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP022Rounded2576]

def sharedSecondN02700MinusPointP023Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP023Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP023RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP023Factor2576
        sharedSecondN02700MinusPointP023Center2576) =
        sharedSecondN02700MinusPointP023Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP023RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP023Rounded2576‖ ≤
          sharedSecondN02700MinusPointP023Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP023Factor2576
      sharedSecondN02700MinusPointP023Center2576)
  rw [sharedSecondN02700MinusPointP023RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP023Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP023Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP023Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP023DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP023Factor2576,
      sharedSecondN02700MinusPointP023Error2576, rounding2542,
      sharedSecondN02700MinusPointP023Radius2576]

theorem sharedSecondN02700MinusPointP023DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP023Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP023RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP023Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP023Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP023Rounded2576]

def sharedSecondN02700MinusPointP024Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP024Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP024RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP024Factor2576
        sharedSecondN02700MinusPointP024Center2576) =
        sharedSecondN02700MinusPointP024Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP024RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP024Rounded2576‖ ≤
          sharedSecondN02700MinusPointP024Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP024Factor2576
      sharedSecondN02700MinusPointP024Center2576)
  rw [sharedSecondN02700MinusPointP024RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP024Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP024Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP024Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP024DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP024Factor2576,
      sharedSecondN02700MinusPointP024Error2576, rounding2542,
      sharedSecondN02700MinusPointP024Radius2576]

theorem sharedSecondN02700MinusPointP024DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP024Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP024RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP024Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP024Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP024Rounded2576]

def sharedSecondN02700MinusPointP025Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP025Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP025RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP025Factor2576
        sharedSecondN02700MinusPointP025Center2576) =
        sharedSecondN02700MinusPointP025Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP025RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP025Rounded2576‖ ≤
          sharedSecondN02700MinusPointP025Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP025Factor2576
      sharedSecondN02700MinusPointP025Center2576)
  rw [sharedSecondN02700MinusPointP025RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP025Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP025Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP025Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP025DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP025Factor2576,
      sharedSecondN02700MinusPointP025Error2576, rounding2542,
      sharedSecondN02700MinusPointP025Radius2576]

theorem sharedSecondN02700MinusPointP025DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP025Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP025RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP025Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP025Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP025Rounded2576]

def sharedSecondN02700MinusPointP026Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP026Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP026RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP026Factor2576
        sharedSecondN02700MinusPointP026Center2576) =
        sharedSecondN02700MinusPointP026Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP026RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP026Rounded2576‖ ≤
          sharedSecondN02700MinusPointP026Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP026Factor2576
      sharedSecondN02700MinusPointP026Center2576)
  rw [sharedSecondN02700MinusPointP026RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP026Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP026Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP026Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP026DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP026Factor2576,
      sharedSecondN02700MinusPointP026Error2576, rounding2542,
      sharedSecondN02700MinusPointP026Radius2576]

theorem sharedSecondN02700MinusPointP026DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP026Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP026RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP026Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP026Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP026Rounded2576]

def sharedSecondN02700MinusPointP027Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP027Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP027RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP027Factor2576
        sharedSecondN02700MinusPointP027Center2576) =
        sharedSecondN02700MinusPointP027Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP027RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP027Rounded2576‖ ≤
          sharedSecondN02700MinusPointP027Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP027Factor2576
      sharedSecondN02700MinusPointP027Center2576)
  rw [sharedSecondN02700MinusPointP027RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP027Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP027Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP027Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP027DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP027Factor2576,
      sharedSecondN02700MinusPointP027Error2576, rounding2542,
      sharedSecondN02700MinusPointP027Radius2576]

theorem sharedSecondN02700MinusPointP027DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP027Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP027RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP027Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP027Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP027Rounded2576]

def sharedSecondN02700MinusPointP028Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP028Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP028RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP028Factor2576
        sharedSecondN02700MinusPointP028Center2576) =
        sharedSecondN02700MinusPointP028Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP028RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP028Rounded2576‖ ≤
          sharedSecondN02700MinusPointP028Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP028Factor2576
      sharedSecondN02700MinusPointP028Center2576)
  rw [sharedSecondN02700MinusPointP028RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP028Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP028Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP028Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP028DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP028Factor2576,
      sharedSecondN02700MinusPointP028Error2576, rounding2542,
      sharedSecondN02700MinusPointP028Radius2576]

theorem sharedSecondN02700MinusPointP028DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP028Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP028RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP028Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP028Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP028Rounded2576]

def sharedSecondN02700MinusPointP029Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700MinusPointP029Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700MinusPointP029RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700MinusPointP029Factor2576
        sharedSecondN02700MinusPointP029Center2576) =
        sharedSecondN02700MinusPointP029Rounded2576 := by
  cbv

theorem sharedSecondN02700MinusPointP029RoundedError2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02700MinusPointPosition2576 -
      embedPair2542 sharedSecondN02700MinusPointP029Rounded2576‖ ≤
          sharedSecondN02700MinusPointP029Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700MinusPointP029Factor2576
      sharedSecondN02700MinusPointP029Center2576)
  rw [sharedSecondN02700MinusPointP029RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP029Factor2576 * embedPair2542
        sharedSecondN02700MinusPointP029Center2576)
    (embedPair2542 sharedSecondN02700MinusPointP029Rounded2576)).trans (add_le_add
        sharedSecondN02700MinusPointP029DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700MinusPointP029Factor2576,
      sharedSecondN02700MinusPointP029Error2576, rounding2542,
      sharedSecondN02700MinusPointP029Radius2576]

theorem sharedSecondN02700MinusPointP029DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02700MinusPointPosition2576‖ ≤ 1 :=
        by
  have h := sharedSecondN02700MinusPoint_triangle2576
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02700MinusPointPosition2576)
    (embedPair2542 sharedSecondN02700MinusPointP029Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700MinusPointP029RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700MinusPointP029Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700MinusPointP029Radius2576, pairMagnitude2542,
      sharedSecondN02700MinusPointP029Rounded2576]

noncomputable def sharedSecondN02700MinusSignedValue2576 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 sharedSecondN02700MinusPointP000Rounded2576
  | 1 => embedPair2542 sharedSecondN02700MinusPointP001Rounded2576
  | 2 => embedPair2542 sharedSecondN02700MinusPointP002Rounded2576
  | 3 => embedPair2542 sharedSecondN02700MinusPointP003Rounded2576
  | 4 => embedPair2542 sharedSecondN02700MinusPointP004Rounded2576
  | 5 => embedPair2542 sharedSecondN02700MinusPointP005Rounded2576
  | 6 => embedPair2542 sharedSecondN02700MinusPointP006Rounded2576
  | 7 => embedPair2542 sharedSecondN02700MinusPointP007Rounded2576
  | 8 => embedPair2542 sharedSecondN02700MinusPointP008Rounded2576
  | 9 => embedPair2542 sharedSecondN02700MinusPointP009Rounded2576
  | 10 => embedPair2542 sharedSecondN02700MinusPointP010Rounded2576
  | 11 => embedPair2542 sharedSecondN02700MinusPointP011Rounded2576
  | 12 => embedPair2542 sharedSecondN02700MinusPointP012Rounded2576
  | 13 => embedPair2542 sharedSecondN02700MinusPointP013Rounded2576
  | 14 => embedPair2542 sharedSecondN02700MinusPointP014Rounded2576
  | 15 => embedPair2542 sharedSecondN02700MinusPointP015Rounded2576
  | 16 => embedPair2542 sharedSecondN02700MinusPointP016Rounded2576
  | 17 => embedPair2542 sharedSecondN02700MinusPointP017Rounded2576
  | 18 => embedPair2542 sharedSecondN02700MinusPointP018Rounded2576
  | 19 => embedPair2542 sharedSecondN02700MinusPointP019Rounded2576
  | 20 => embedPair2542 sharedSecondN02700MinusPointP020Rounded2576
  | 21 => embedPair2542 sharedSecondN02700MinusPointP021Rounded2576
  | 22 => embedPair2542 sharedSecondN02700MinusPointP022Rounded2576
  | 23 => embedPair2542 sharedSecondN02700MinusPointP023Rounded2576
  | 24 => embedPair2542 sharedSecondN02700MinusPointP024Rounded2576
  | 25 => embedPair2542 sharedSecondN02700MinusPointP025Rounded2576
  | 26 => embedPair2542 sharedSecondN02700MinusPointP026Rounded2576
  | 27 => embedPair2542 sharedSecondN02700MinusPointP027Rounded2576
  | 28 => embedPair2542 sharedSecondN02700MinusPointP028Rounded2576
  | 29 => embedPair2542 sharedSecondN02700MinusPointP029Rounded2576
  | _ => 0

noncomputable def sharedSecondN02700MinusSignedError2576 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => sharedSecondN02700MinusPointP000Radius2576
  | 1 => sharedSecondN02700MinusPointP001Radius2576
  | 2 => sharedSecondN02700MinusPointP002Radius2576
  | 3 => sharedSecondN02700MinusPointP003Radius2576
  | 4 => sharedSecondN02700MinusPointP004Radius2576
  | 5 => sharedSecondN02700MinusPointP005Radius2576
  | 6 => sharedSecondN02700MinusPointP006Radius2576
  | 7 => sharedSecondN02700MinusPointP007Radius2576
  | 8 => sharedSecondN02700MinusPointP008Radius2576
  | 9 => sharedSecondN02700MinusPointP009Radius2576
  | 10 => sharedSecondN02700MinusPointP010Radius2576
  | 11 => sharedSecondN02700MinusPointP011Radius2576
  | 12 => sharedSecondN02700MinusPointP012Radius2576
  | 13 => sharedSecondN02700MinusPointP013Radius2576
  | 14 => sharedSecondN02700MinusPointP014Radius2576
  | 15 => sharedSecondN02700MinusPointP015Radius2576
  | 16 => sharedSecondN02700MinusPointP016Radius2576
  | 17 => sharedSecondN02700MinusPointP017Radius2576
  | 18 => sharedSecondN02700MinusPointP018Radius2576
  | 19 => sharedSecondN02700MinusPointP019Radius2576
  | 20 => sharedSecondN02700MinusPointP020Radius2576
  | 21 => sharedSecondN02700MinusPointP021Radius2576
  | 22 => sharedSecondN02700MinusPointP022Radius2576
  | 23 => sharedSecondN02700MinusPointP023Radius2576
  | 24 => sharedSecondN02700MinusPointP024Radius2576
  | 25 => sharedSecondN02700MinusPointP025Radius2576
  | 26 => sharedSecondN02700MinusPointP026Radius2576
  | 27 => sharedSecondN02700MinusPointP027Radius2576
  | 28 => sharedSecondN02700MinusPointP028Radius2576
  | 29 => sharedSecondN02700MinusPointP029Radius2576
  | _ => 0

theorem sharedSecondN02700MinusSignedExpError2576 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i sharedSecondN02700MinusPointPosition2576 -
        sharedSecondN02700MinusSignedValue2576 i‖ ≤ sharedSecondN02700MinusSignedError2576 i := by
  fin_cases i
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP000RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP001RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP002RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP003RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP004RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP005RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP006RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP007RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP008RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP009RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP010RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP011RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP012RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP013RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP014RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP015RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP016RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP017RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP018RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP019RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP020RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP021RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP022RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP023RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP024RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP025RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP026RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP027RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP028RoundedError2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP029RoundedError2576

theorem sharedSecondN02700MinusSignedUnitNorm2576 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i sharedSecondN02700MinusPointPosition2576‖ ≤
        1
        := by
  fin_cases i
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP000DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP001DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP002DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP003DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP004DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP005DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP006DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP007DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP008DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP009DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP010DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP011DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP012DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP013DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP014DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP015DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP016DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP017DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP018DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP019DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP020DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP021DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP022DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP023DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP024DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP025DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP026DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP027DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP028DerivativeNorm2576
  · simpa only [sharedSecondN02700MinusSignedValue2576, sharedSecondN02700MinusSignedError2576]
      using
      sharedSecondN02700MinusPointP029DerivativeNorm2576

noncomputable def sharedSecondN02700MinusSignedSum2576 : ℂ := ⟨(((-(((4098573425992 * 10^40
        + 5557890842551430698179043038899578147337) * 10^40
        + 5598945337423269590942411020930640280775) * 10^40
        + 6050917677958924351165737855004024597745)) : ℝ) /
        (((177450860423 * 10^40
        + 7321510130185077851573570199319728240522) * 10^40
        + 6081091069315933576369956003987455836199) * 10^40
        + 664932998233037501529828597054346100736)),
    (((((11018308014180 * 10^40
        + 7742351255805448255723500921731444853727) * 10^40
        + 8235737906340028488031852515910756561240) * 10^40
        + 253811236306514168490439126912802381193) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888))⟩

noncomputable def sharedSecondN02700MinusSignedUpper2576 : ℝ := ((1218308507 : ℝ) /
        50000000)

theorem sharedSecondN02700MinusSignedSum_eq2576 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * sharedSecondN02700MinusSignedValue2576 i) =
      sharedSecondN02700MinusSignedSum2576 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        sharedSecondN02700MinusSignedValue2576,
      sharedSecondN02700MinusSignedSum2576, embedPair2542,
          sharedSecondN02700MinusPointP000Rounded2576,
      sharedSecondN02700MinusPointP001Rounded2576,
      sharedSecondN02700MinusPointP002Rounded2576,
      sharedSecondN02700MinusPointP003Rounded2576,
      sharedSecondN02700MinusPointP004Rounded2576,
      sharedSecondN02700MinusPointP005Rounded2576,
      sharedSecondN02700MinusPointP006Rounded2576,
      sharedSecondN02700MinusPointP007Rounded2576,
      sharedSecondN02700MinusPointP008Rounded2576,
      sharedSecondN02700MinusPointP009Rounded2576,
      sharedSecondN02700MinusPointP010Rounded2576,
      sharedSecondN02700MinusPointP011Rounded2576,
      sharedSecondN02700MinusPointP012Rounded2576,
      sharedSecondN02700MinusPointP013Rounded2576,
      sharedSecondN02700MinusPointP014Rounded2576,
      sharedSecondN02700MinusPointP015Rounded2576,
      sharedSecondN02700MinusPointP016Rounded2576,
      sharedSecondN02700MinusPointP017Rounded2576,
      sharedSecondN02700MinusPointP018Rounded2576,
      sharedSecondN02700MinusPointP019Rounded2576,
      sharedSecondN02700MinusPointP020Rounded2576,
      sharedSecondN02700MinusPointP021Rounded2576,
      sharedSecondN02700MinusPointP022Rounded2576,
      sharedSecondN02700MinusPointP023Rounded2576,
      sharedSecondN02700MinusPointP024Rounded2576,
      sharedSecondN02700MinusPointP025Rounded2576,
      sharedSecondN02700MinusPointP026Rounded2576,
      sharedSecondN02700MinusPointP027Rounded2576,
      sharedSecondN02700MinusPointP028Rounded2576,
      sharedSecondN02700MinusPointP029Rounded2576, Complex.mul_re, Complex.mul_im]

theorem sharedSecondN02700MinusSignedSum_norm2576 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * sharedSecondN02700MinusSignedValue2576 i‖ ≤
        ((609154251 :
        ℝ) /
        25000000) := by
  rw [sharedSecondN02700MinusSignedSum_eq2576]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [sharedSecondN02700MinusSignedSum2576]

theorem sharedSecondN02700MinusSignedCharge2576 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * sharedSecondN02700MinusSignedError2576 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      sharedSecondN02700MinusSignedError2576, sharedSecondN02700MinusPointP000Radius2576,
      sharedSecondN02700MinusPointP001Radius2576,
      sharedSecondN02700MinusPointP002Radius2576,
      sharedSecondN02700MinusPointP003Radius2576,
      sharedSecondN02700MinusPointP004Radius2576,
      sharedSecondN02700MinusPointP005Radius2576,
      sharedSecondN02700MinusPointP006Radius2576,
      sharedSecondN02700MinusPointP007Radius2576,
      sharedSecondN02700MinusPointP008Radius2576,
      sharedSecondN02700MinusPointP009Radius2576,
      sharedSecondN02700MinusPointP010Radius2576,
      sharedSecondN02700MinusPointP011Radius2576,
      sharedSecondN02700MinusPointP012Radius2576,
      sharedSecondN02700MinusPointP013Radius2576,
      sharedSecondN02700MinusPointP014Radius2576,
      sharedSecondN02700MinusPointP015Radius2576,
      sharedSecondN02700MinusPointP016Radius2576,
      sharedSecondN02700MinusPointP017Radius2576,
      sharedSecondN02700MinusPointP018Radius2576,
      sharedSecondN02700MinusPointP019Radius2576,
      sharedSecondN02700MinusPointP020Radius2576,
      sharedSecondN02700MinusPointP021Radius2576,
      sharedSecondN02700MinusPointP022Radius2576,
      sharedSecondN02700MinusPointP023Radius2576,
      sharedSecondN02700MinusPointP024Radius2576,
      sharedSecondN02700MinusPointP025Radius2576,
      sharedSecondN02700MinusPointP026Radius2576,
      sharedSecondN02700MinusPointP027Radius2576,
      sharedSecondN02700MinusPointP028Radius2576,
      sharedSecondN02700MinusPointP029Radius2576]

theorem sharedSecondN02700MinusSignedUpper_le2576 :
    signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 sharedSecondN02700MinusPointPosition2576 ≤
          sharedSecondN02700MinusSignedUpper2576 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i
            sharedSecondN02700MinusPointPosition2576‖
            ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * sharedSecondN02700MinusSignedValue2576 i‖
          +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * sharedSecondN02700MinusSignedError2576 i :=
              by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (sharedSecondN02700MinusSignedExpError2576 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i sharedSecondN02700MinusPointPosition2576‖
          ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (sharedSecondN02700MinusSignedUnitNorm2576 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i
          sharedSecondN02700MinusPointPosition2576‖)
          ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 sharedSecondN02700MinusSignedUpper2576
  linarith [sharedSecondN02700MinusSignedSum_norm2576, sharedSecondN02700MinusSignedCharge2576]

theorem sharedSecondN02700MinusPhysical2576 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        sharedSecondN02700MinusPointPosition2576‖ ≤
      sharedSecondN02700MinusSignedUpper2576 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        sharedSecondN02700MinusPointPosition2576
  exact h.trans sharedSecondN02700MinusSignedUpper_le2576

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.sharedSecondN02700MinusSignedExpError2576
#print axioms ConnesWeilRH.Dev.sharedSecondN02700MinusSignedSum_eq2576
#print axioms ConnesWeilRH.Dev.sharedSecondN02700MinusSignedCharge2576
#print axioms ConnesWeilRH.Dev.sharedSecondN02700MinusSignedUpper_le2576
#print axioms ConnesWeilRH.Dev.sharedSecondN02700MinusPhysical2576
