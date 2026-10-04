import ConnesWeilRH.Dev.C1RouteACorrSecondN02700MinusDerivatives2575
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem corrSecondN02700MinusPoint_triangle2575 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def corrSecondN02700MinusPointP000Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP000Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP000RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP000Factor2575
        corrSecondN02700MinusPointP000Center2575) =
        corrSecondN02700MinusPointP000Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP000RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP000Rounded2575‖ ≤
          corrSecondN02700MinusPointP000Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP000Factor2575
      corrSecondN02700MinusPointP000Center2575)
  rw [corrSecondN02700MinusPointP000RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP000Factor2575 * embedPair2542
        corrSecondN02700MinusPointP000Center2575)
    (embedPair2542 corrSecondN02700MinusPointP000Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP000DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP000Factor2575,
      corrSecondN02700MinusPointP000Error2575, rounding2542,
      corrSecondN02700MinusPointP000Radius2575]

theorem corrSecondN02700MinusPointP000DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP000Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP000RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP000Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP000Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP000Rounded2575]

def corrSecondN02700MinusPointP001Rounded2575 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP001Radius2575 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02700MinusPointP001RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP001Factor2575
        corrSecondN02700MinusPointP001Center2575) =
        corrSecondN02700MinusPointP001Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP001RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP001Rounded2575‖ ≤
          corrSecondN02700MinusPointP001Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP001Factor2575
      corrSecondN02700MinusPointP001Center2575)
  rw [corrSecondN02700MinusPointP001RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP001Factor2575 * embedPair2542
        corrSecondN02700MinusPointP001Center2575)
    (embedPair2542 corrSecondN02700MinusPointP001Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP001DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP001Factor2575,
      corrSecondN02700MinusPointP001Error2575, rounding2542,
      corrSecondN02700MinusPointP001Radius2575]

theorem corrSecondN02700MinusPointP001DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP001Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP001RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP001Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP001Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP001Rounded2575]

def corrSecondN02700MinusPointP002Rounded2575 : RatPair2542 :=
  (((28161701 : ℚ) /
        1267650600228229401496703205376),
    (((-11070949) : ℚ) /
        633825300114114700748351602688))

noncomputable def corrSecondN02700MinusPointP002Radius2575 : ℝ := ((2199023390103 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02700MinusPointP002RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP002Factor2575
        corrSecondN02700MinusPointP002Center2575) =
        corrSecondN02700MinusPointP002Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP002RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP002Rounded2575‖ ≤
          corrSecondN02700MinusPointP002Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP002Factor2575
      corrSecondN02700MinusPointP002Center2575)
  rw [corrSecondN02700MinusPointP002RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP002Factor2575 * embedPair2542
        corrSecondN02700MinusPointP002Center2575)
    (embedPair2542 corrSecondN02700MinusPointP002Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP002DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP002Factor2575,
      corrSecondN02700MinusPointP002Error2575, rounding2542,
      corrSecondN02700MinusPointP002Radius2575]

theorem corrSecondN02700MinusPointP002DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP002Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP002RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP002Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP002Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP002Rounded2575]

def corrSecondN02700MinusPointP003Rounded2575 : RatPair2542 :=
  (((82964876946047 : ℚ) /
        316912650057057350374175801344),
    ((5530890319949 : ℚ) /
        79228162514264337593543950336))

noncomputable def corrSecondN02700MinusPointP003Radius2575 : ℝ := ((962463443223 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrSecondN02700MinusPointP003RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP003Factor2575
        corrSecondN02700MinusPointP003Center2575) =
        corrSecondN02700MinusPointP003Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP003RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP003Rounded2575‖ ≤
          corrSecondN02700MinusPointP003Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP003Factor2575
      corrSecondN02700MinusPointP003Center2575)
  rw [corrSecondN02700MinusPointP003RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP003Factor2575 * embedPair2542
        corrSecondN02700MinusPointP003Center2575)
    (embedPair2542 corrSecondN02700MinusPointP003Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP003DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP003Factor2575,
      corrSecondN02700MinusPointP003Error2575, rounding2542,
      corrSecondN02700MinusPointP003Radius2575]

theorem corrSecondN02700MinusPointP003DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP003Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP003RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP003Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP003Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP003Rounded2575]

def corrSecondN02700MinusPointP004Rounded2575 : RatPair2542 :=
  (((32763306632307601 : ℚ) /
        316912650057057350374175801344),
    (((-89250173431151475) : ℚ) /
        1267650600228229401496703205376))

noncomputable def corrSecondN02700MinusPointP004Radius2575 : ℝ := ((676340962967073 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02700MinusPointP004RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP004Factor2575
        corrSecondN02700MinusPointP004Center2575) =
        corrSecondN02700MinusPointP004Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP004RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP004Rounded2575‖ ≤
          corrSecondN02700MinusPointP004Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP004Factor2575
      corrSecondN02700MinusPointP004Center2575)
  rw [corrSecondN02700MinusPointP004RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP004Factor2575 * embedPair2542
        corrSecondN02700MinusPointP004Center2575)
    (embedPair2542 corrSecondN02700MinusPointP004Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP004DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP004Factor2575,
      corrSecondN02700MinusPointP004Error2575, rounding2542,
      corrSecondN02700MinusPointP004Radius2575]

theorem corrSecondN02700MinusPointP004DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP004Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP004RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP004Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP004Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP004Rounded2575]

def corrSecondN02700MinusPointP005Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP005Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP005RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP005Factor2575
        corrSecondN02700MinusPointP005Center2575) =
        corrSecondN02700MinusPointP005Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP005RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP005Rounded2575‖ ≤
          corrSecondN02700MinusPointP005Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP005Factor2575
      corrSecondN02700MinusPointP005Center2575)
  rw [corrSecondN02700MinusPointP005RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP005Factor2575 * embedPair2542
        corrSecondN02700MinusPointP005Center2575)
    (embedPair2542 corrSecondN02700MinusPointP005Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP005DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP005Factor2575,
      corrSecondN02700MinusPointP005Error2575, rounding2542,
      corrSecondN02700MinusPointP005Radius2575]

theorem corrSecondN02700MinusPointP005DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP005Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP005RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP005Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP005Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP005Rounded2575]

def corrSecondN02700MinusPointP006Rounded2575 : RatPair2542 :=
  (((21 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP006Radius2575 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02700MinusPointP006RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP006Factor2575
        corrSecondN02700MinusPointP006Center2575) =
        corrSecondN02700MinusPointP006Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP006RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP006Rounded2575‖ ≤
          corrSecondN02700MinusPointP006Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP006Factor2575
      corrSecondN02700MinusPointP006Center2575)
  rw [corrSecondN02700MinusPointP006RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP006Factor2575 * embedPair2542
        corrSecondN02700MinusPointP006Center2575)
    (embedPair2542 corrSecondN02700MinusPointP006Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP006DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP006Factor2575,
      corrSecondN02700MinusPointP006Error2575, rounding2542,
      corrSecondN02700MinusPointP006Radius2575]

theorem corrSecondN02700MinusPointP006DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP006Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP006RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP006Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP006Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP006Rounded2575]

def corrSecondN02700MinusPointP007Rounded2575 : RatPair2542 :=
  (((17518673253473 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP007Radius2575 : ℝ := ((2203873831015 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02700MinusPointP007RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP007Factor2575
        corrSecondN02700MinusPointP007Center2575) =
        corrSecondN02700MinusPointP007Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP007RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP007Rounded2575‖ ≤
          corrSecondN02700MinusPointP007Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP007Factor2575
      corrSecondN02700MinusPointP007Center2575)
  rw [corrSecondN02700MinusPointP007RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP007Factor2575 * embedPair2542
        corrSecondN02700MinusPointP007Center2575)
    (embedPair2542 corrSecondN02700MinusPointP007Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP007DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP007Factor2575,
      corrSecondN02700MinusPointP007Error2575, rounding2542,
      corrSecondN02700MinusPointP007Radius2575]

theorem corrSecondN02700MinusPointP007DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP007Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP007RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP007Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP007Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP007Rounded2575]

def corrSecondN02700MinusPointP008Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP008Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP008RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP008Factor2575
        corrSecondN02700MinusPointP008Center2575) =
        corrSecondN02700MinusPointP008Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP008RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP008Rounded2575‖ ≤
          corrSecondN02700MinusPointP008Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP008Factor2575
      corrSecondN02700MinusPointP008Center2575)
  rw [corrSecondN02700MinusPointP008RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP008Factor2575 * embedPair2542
        corrSecondN02700MinusPointP008Center2575)
    (embedPair2542 corrSecondN02700MinusPointP008Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP008DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP008Factor2575,
      corrSecondN02700MinusPointP008Error2575, rounding2542,
      corrSecondN02700MinusPointP008Radius2575]

theorem corrSecondN02700MinusPointP008DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP008Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP008RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP008Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP008Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP008Rounded2575]

def corrSecondN02700MinusPointP009Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP009Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP009RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP009Factor2575
        corrSecondN02700MinusPointP009Center2575) =
        corrSecondN02700MinusPointP009Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP009RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP009Rounded2575‖ ≤
          corrSecondN02700MinusPointP009Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP009Factor2575
      corrSecondN02700MinusPointP009Center2575)
  rw [corrSecondN02700MinusPointP009RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP009Factor2575 * embedPair2542
        corrSecondN02700MinusPointP009Center2575)
    (embedPair2542 corrSecondN02700MinusPointP009Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP009DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP009Factor2575,
      corrSecondN02700MinusPointP009Error2575, rounding2542,
      corrSecondN02700MinusPointP009Radius2575]

theorem corrSecondN02700MinusPointP009DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP009Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP009RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP009Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP009Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP009Rounded2575]

def corrSecondN02700MinusPointP010Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP010Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP010RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP010Factor2575
        corrSecondN02700MinusPointP010Center2575) =
        corrSecondN02700MinusPointP010Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP010RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP010Rounded2575‖ ≤
          corrSecondN02700MinusPointP010Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP010Factor2575
      corrSecondN02700MinusPointP010Center2575)
  rw [corrSecondN02700MinusPointP010RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP010Factor2575 * embedPair2542
        corrSecondN02700MinusPointP010Center2575)
    (embedPair2542 corrSecondN02700MinusPointP010Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP010DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP010Factor2575,
      corrSecondN02700MinusPointP010Error2575, rounding2542,
      corrSecondN02700MinusPointP010Radius2575]

theorem corrSecondN02700MinusPointP010DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP010Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP010RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP010Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP010Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP010Rounded2575]

def corrSecondN02700MinusPointP011Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP011Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP011RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP011Factor2575
        corrSecondN02700MinusPointP011Center2575) =
        corrSecondN02700MinusPointP011Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP011RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP011Rounded2575‖ ≤
          corrSecondN02700MinusPointP011Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP011Factor2575
      corrSecondN02700MinusPointP011Center2575)
  rw [corrSecondN02700MinusPointP011RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP011Factor2575 * embedPair2542
        corrSecondN02700MinusPointP011Center2575)
    (embedPair2542 corrSecondN02700MinusPointP011Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP011DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP011Factor2575,
      corrSecondN02700MinusPointP011Error2575, rounding2542,
      corrSecondN02700MinusPointP011Radius2575]

theorem corrSecondN02700MinusPointP011DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP011Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP011RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP011Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP011Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP011Rounded2575]

def corrSecondN02700MinusPointP012Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP012Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP012RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP012Factor2575
        corrSecondN02700MinusPointP012Center2575) =
        corrSecondN02700MinusPointP012Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP012RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP012Rounded2575‖ ≤
          corrSecondN02700MinusPointP012Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP012Factor2575
      corrSecondN02700MinusPointP012Center2575)
  rw [corrSecondN02700MinusPointP012RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP012Factor2575 * embedPair2542
        corrSecondN02700MinusPointP012Center2575)
    (embedPair2542 corrSecondN02700MinusPointP012Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP012DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP012Factor2575,
      corrSecondN02700MinusPointP012Error2575, rounding2542,
      corrSecondN02700MinusPointP012Radius2575]

theorem corrSecondN02700MinusPointP012DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP012Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP012RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP012Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP012Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP012Rounded2575]

def corrSecondN02700MinusPointP013Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP013Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP013RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP013Factor2575
        corrSecondN02700MinusPointP013Center2575) =
        corrSecondN02700MinusPointP013Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP013RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP013Rounded2575‖ ≤
          corrSecondN02700MinusPointP013Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP013Factor2575
      corrSecondN02700MinusPointP013Center2575)
  rw [corrSecondN02700MinusPointP013RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP013Factor2575 * embedPair2542
        corrSecondN02700MinusPointP013Center2575)
    (embedPair2542 corrSecondN02700MinusPointP013Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP013DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP013Factor2575,
      corrSecondN02700MinusPointP013Error2575, rounding2542,
      corrSecondN02700MinusPointP013Radius2575]

theorem corrSecondN02700MinusPointP013DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP013Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP013RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP013Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP013Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP013Rounded2575]

def corrSecondN02700MinusPointP014Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP014Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP014RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP014Factor2575
        corrSecondN02700MinusPointP014Center2575) =
        corrSecondN02700MinusPointP014Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP014RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP014Rounded2575‖ ≤
          corrSecondN02700MinusPointP014Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP014Factor2575
      corrSecondN02700MinusPointP014Center2575)
  rw [corrSecondN02700MinusPointP014RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP014Factor2575 * embedPair2542
        corrSecondN02700MinusPointP014Center2575)
    (embedPair2542 corrSecondN02700MinusPointP014Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP014DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP014Factor2575,
      corrSecondN02700MinusPointP014Error2575, rounding2542,
      corrSecondN02700MinusPointP014Radius2575]

theorem corrSecondN02700MinusPointP014DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP014Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP014RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP014Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP014Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP014Rounded2575]

def corrSecondN02700MinusPointP015Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP015Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP015RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP015Factor2575
        corrSecondN02700MinusPointP015Center2575) =
        corrSecondN02700MinusPointP015Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP015RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP015Rounded2575‖ ≤
          corrSecondN02700MinusPointP015Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP015Factor2575
      corrSecondN02700MinusPointP015Center2575)
  rw [corrSecondN02700MinusPointP015RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP015Factor2575 * embedPair2542
        corrSecondN02700MinusPointP015Center2575)
    (embedPair2542 corrSecondN02700MinusPointP015Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP015DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP015Factor2575,
      corrSecondN02700MinusPointP015Error2575, rounding2542,
      corrSecondN02700MinusPointP015Radius2575]

theorem corrSecondN02700MinusPointP015DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP015Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP015RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP015Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP015Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP015Rounded2575]

def corrSecondN02700MinusPointP016Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP016Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP016RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP016Factor2575
        corrSecondN02700MinusPointP016Center2575) =
        corrSecondN02700MinusPointP016Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP016RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP016Rounded2575‖ ≤
          corrSecondN02700MinusPointP016Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP016Factor2575
      corrSecondN02700MinusPointP016Center2575)
  rw [corrSecondN02700MinusPointP016RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP016Factor2575 * embedPair2542
        corrSecondN02700MinusPointP016Center2575)
    (embedPair2542 corrSecondN02700MinusPointP016Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP016DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP016Factor2575,
      corrSecondN02700MinusPointP016Error2575, rounding2542,
      corrSecondN02700MinusPointP016Radius2575]

theorem corrSecondN02700MinusPointP016DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP016Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP016RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP016Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP016Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP016Rounded2575]

def corrSecondN02700MinusPointP017Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP017Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP017RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP017Factor2575
        corrSecondN02700MinusPointP017Center2575) =
        corrSecondN02700MinusPointP017Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP017RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP017Rounded2575‖ ≤
          corrSecondN02700MinusPointP017Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP017Factor2575
      corrSecondN02700MinusPointP017Center2575)
  rw [corrSecondN02700MinusPointP017RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP017Factor2575 * embedPair2542
        corrSecondN02700MinusPointP017Center2575)
    (embedPair2542 corrSecondN02700MinusPointP017Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP017DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP017Factor2575,
      corrSecondN02700MinusPointP017Error2575, rounding2542,
      corrSecondN02700MinusPointP017Radius2575]

theorem corrSecondN02700MinusPointP017DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP017Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP017RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP017Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP017Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP017Rounded2575]

def corrSecondN02700MinusPointP018Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP018Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP018RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP018Factor2575
        corrSecondN02700MinusPointP018Center2575) =
        corrSecondN02700MinusPointP018Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP018RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP018Rounded2575‖ ≤
          corrSecondN02700MinusPointP018Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP018Factor2575
      corrSecondN02700MinusPointP018Center2575)
  rw [corrSecondN02700MinusPointP018RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP018Factor2575 * embedPair2542
        corrSecondN02700MinusPointP018Center2575)
    (embedPair2542 corrSecondN02700MinusPointP018Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP018DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP018Factor2575,
      corrSecondN02700MinusPointP018Error2575, rounding2542,
      corrSecondN02700MinusPointP018Radius2575]

theorem corrSecondN02700MinusPointP018DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP018Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP018RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP018Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP018Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP018Rounded2575]

def corrSecondN02700MinusPointP019Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP019Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP019RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP019Factor2575
        corrSecondN02700MinusPointP019Center2575) =
        corrSecondN02700MinusPointP019Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP019RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP019Rounded2575‖ ≤
          corrSecondN02700MinusPointP019Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP019Factor2575
      corrSecondN02700MinusPointP019Center2575)
  rw [corrSecondN02700MinusPointP019RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP019Factor2575 * embedPair2542
        corrSecondN02700MinusPointP019Center2575)
    (embedPair2542 corrSecondN02700MinusPointP019Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP019DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP019Factor2575,
      corrSecondN02700MinusPointP019Error2575, rounding2542,
      corrSecondN02700MinusPointP019Radius2575]

theorem corrSecondN02700MinusPointP019DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP019Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP019RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP019Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP019Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP019Rounded2575]

def corrSecondN02700MinusPointP020Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP020Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP020RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP020Factor2575
        corrSecondN02700MinusPointP020Center2575) =
        corrSecondN02700MinusPointP020Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP020RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP020Rounded2575‖ ≤
          corrSecondN02700MinusPointP020Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP020Factor2575
      corrSecondN02700MinusPointP020Center2575)
  rw [corrSecondN02700MinusPointP020RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP020Factor2575 * embedPair2542
        corrSecondN02700MinusPointP020Center2575)
    (embedPair2542 corrSecondN02700MinusPointP020Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP020DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP020Factor2575,
      corrSecondN02700MinusPointP020Error2575, rounding2542,
      corrSecondN02700MinusPointP020Radius2575]

theorem corrSecondN02700MinusPointP020DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP020Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP020RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP020Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP020Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP020Rounded2575]

def corrSecondN02700MinusPointP021Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP021Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP021RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP021Factor2575
        corrSecondN02700MinusPointP021Center2575) =
        corrSecondN02700MinusPointP021Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP021RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP021Rounded2575‖ ≤
          corrSecondN02700MinusPointP021Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP021Factor2575
      corrSecondN02700MinusPointP021Center2575)
  rw [corrSecondN02700MinusPointP021RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP021Factor2575 * embedPair2542
        corrSecondN02700MinusPointP021Center2575)
    (embedPair2542 corrSecondN02700MinusPointP021Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP021DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP021Factor2575,
      corrSecondN02700MinusPointP021Error2575, rounding2542,
      corrSecondN02700MinusPointP021Radius2575]

theorem corrSecondN02700MinusPointP021DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP021Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP021RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP021Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP021Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP021Rounded2575]

def corrSecondN02700MinusPointP022Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP022Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP022RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP022Factor2575
        corrSecondN02700MinusPointP022Center2575) =
        corrSecondN02700MinusPointP022Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP022RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP022Rounded2575‖ ≤
          corrSecondN02700MinusPointP022Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP022Factor2575
      corrSecondN02700MinusPointP022Center2575)
  rw [corrSecondN02700MinusPointP022RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP022Factor2575 * embedPair2542
        corrSecondN02700MinusPointP022Center2575)
    (embedPair2542 corrSecondN02700MinusPointP022Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP022DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP022Factor2575,
      corrSecondN02700MinusPointP022Error2575, rounding2542,
      corrSecondN02700MinusPointP022Radius2575]

theorem corrSecondN02700MinusPointP022DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP022Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP022RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP022Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP022Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP022Rounded2575]

def corrSecondN02700MinusPointP023Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP023Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP023RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP023Factor2575
        corrSecondN02700MinusPointP023Center2575) =
        corrSecondN02700MinusPointP023Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP023RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP023Rounded2575‖ ≤
          corrSecondN02700MinusPointP023Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP023Factor2575
      corrSecondN02700MinusPointP023Center2575)
  rw [corrSecondN02700MinusPointP023RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP023Factor2575 * embedPair2542
        corrSecondN02700MinusPointP023Center2575)
    (embedPair2542 corrSecondN02700MinusPointP023Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP023DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP023Factor2575,
      corrSecondN02700MinusPointP023Error2575, rounding2542,
      corrSecondN02700MinusPointP023Radius2575]

theorem corrSecondN02700MinusPointP023DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP023Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP023RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP023Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP023Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP023Rounded2575]

def corrSecondN02700MinusPointP024Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP024Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP024RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP024Factor2575
        corrSecondN02700MinusPointP024Center2575) =
        corrSecondN02700MinusPointP024Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP024RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP024Rounded2575‖ ≤
          corrSecondN02700MinusPointP024Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP024Factor2575
      corrSecondN02700MinusPointP024Center2575)
  rw [corrSecondN02700MinusPointP024RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP024Factor2575 * embedPair2542
        corrSecondN02700MinusPointP024Center2575)
    (embedPair2542 corrSecondN02700MinusPointP024Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP024DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP024Factor2575,
      corrSecondN02700MinusPointP024Error2575, rounding2542,
      corrSecondN02700MinusPointP024Radius2575]

theorem corrSecondN02700MinusPointP024DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP024Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP024RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP024Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP024Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP024Rounded2575]

def corrSecondN02700MinusPointP025Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP025Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP025RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP025Factor2575
        corrSecondN02700MinusPointP025Center2575) =
        corrSecondN02700MinusPointP025Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP025RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP025Rounded2575‖ ≤
          corrSecondN02700MinusPointP025Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP025Factor2575
      corrSecondN02700MinusPointP025Center2575)
  rw [corrSecondN02700MinusPointP025RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP025Factor2575 * embedPair2542
        corrSecondN02700MinusPointP025Center2575)
    (embedPair2542 corrSecondN02700MinusPointP025Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP025DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP025Factor2575,
      corrSecondN02700MinusPointP025Error2575, rounding2542,
      corrSecondN02700MinusPointP025Radius2575]

theorem corrSecondN02700MinusPointP025DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP025Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP025RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP025Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP025Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP025Rounded2575]

def corrSecondN02700MinusPointP026Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP026Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP026RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP026Factor2575
        corrSecondN02700MinusPointP026Center2575) =
        corrSecondN02700MinusPointP026Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP026RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP026Rounded2575‖ ≤
          corrSecondN02700MinusPointP026Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP026Factor2575
      corrSecondN02700MinusPointP026Center2575)
  rw [corrSecondN02700MinusPointP026RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP026Factor2575 * embedPair2542
        corrSecondN02700MinusPointP026Center2575)
    (embedPair2542 corrSecondN02700MinusPointP026Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP026DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP026Factor2575,
      corrSecondN02700MinusPointP026Error2575, rounding2542,
      corrSecondN02700MinusPointP026Radius2575]

theorem corrSecondN02700MinusPointP026DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP026Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP026RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP026Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP026Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP026Rounded2575]

def corrSecondN02700MinusPointP027Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP027Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP027RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP027Factor2575
        corrSecondN02700MinusPointP027Center2575) =
        corrSecondN02700MinusPointP027Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP027RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP027Rounded2575‖ ≤
          corrSecondN02700MinusPointP027Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP027Factor2575
      corrSecondN02700MinusPointP027Center2575)
  rw [corrSecondN02700MinusPointP027RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP027Factor2575 * embedPair2542
        corrSecondN02700MinusPointP027Center2575)
    (embedPair2542 corrSecondN02700MinusPointP027Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP027DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP027Factor2575,
      corrSecondN02700MinusPointP027Error2575, rounding2542,
      corrSecondN02700MinusPointP027Radius2575]

theorem corrSecondN02700MinusPointP027DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP027Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP027RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP027Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP027Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP027Rounded2575]

def corrSecondN02700MinusPointP028Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP028Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP028RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP028Factor2575
        corrSecondN02700MinusPointP028Center2575) =
        corrSecondN02700MinusPointP028Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP028RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP028Rounded2575‖ ≤
          corrSecondN02700MinusPointP028Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP028Factor2575
      corrSecondN02700MinusPointP028Center2575)
  rw [corrSecondN02700MinusPointP028RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP028Factor2575 * embedPair2542
        corrSecondN02700MinusPointP028Center2575)
    (embedPair2542 corrSecondN02700MinusPointP028Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP028DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP028Factor2575,
      corrSecondN02700MinusPointP028Error2575, rounding2542,
      corrSecondN02700MinusPointP028Radius2575]

theorem corrSecondN02700MinusPointP028DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP028Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP028RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP028Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP028Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP028Rounded2575]

def corrSecondN02700MinusPointP029Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700MinusPointP029Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700MinusPointP029RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700MinusPointP029Factor2575
        corrSecondN02700MinusPointP029Center2575) =
        corrSecondN02700MinusPointP029Rounded2575 := by
  cbv

theorem corrSecondN02700MinusPointP029RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02700MinusPointPosition2575 -
      embedPair2542 corrSecondN02700MinusPointP029Rounded2575‖ ≤
          corrSecondN02700MinusPointP029Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700MinusPointP029Factor2575
      corrSecondN02700MinusPointP029Center2575)
  rw [corrSecondN02700MinusPointP029RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP029Factor2575 * embedPair2542
        corrSecondN02700MinusPointP029Center2575)
    (embedPair2542 corrSecondN02700MinusPointP029Rounded2575)).trans (add_le_add
        corrSecondN02700MinusPointP029DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700MinusPointP029Factor2575,
      corrSecondN02700MinusPointP029Error2575, rounding2542,
      corrSecondN02700MinusPointP029Radius2575]

theorem corrSecondN02700MinusPointP029DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02700MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02700MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02700MinusPointPosition2575)
    (embedPair2542 corrSecondN02700MinusPointP029Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700MinusPointP029RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700MinusPointP029Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700MinusPointP029Radius2575, pairMagnitude2542,
      corrSecondN02700MinusPointP029Rounded2575]

noncomputable def corrSecondN02700MinusSignedValue2575 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 corrSecondN02700MinusPointP000Rounded2575
  | 1 => embedPair2542 corrSecondN02700MinusPointP001Rounded2575
  | 2 => embedPair2542 corrSecondN02700MinusPointP002Rounded2575
  | 3 => embedPair2542 corrSecondN02700MinusPointP003Rounded2575
  | 4 => embedPair2542 corrSecondN02700MinusPointP004Rounded2575
  | 5 => embedPair2542 corrSecondN02700MinusPointP005Rounded2575
  | 6 => embedPair2542 corrSecondN02700MinusPointP006Rounded2575
  | 7 => embedPair2542 corrSecondN02700MinusPointP007Rounded2575
  | 8 => embedPair2542 corrSecondN02700MinusPointP008Rounded2575
  | 9 => embedPair2542 corrSecondN02700MinusPointP009Rounded2575
  | 10 => embedPair2542 corrSecondN02700MinusPointP010Rounded2575
  | 11 => embedPair2542 corrSecondN02700MinusPointP011Rounded2575
  | 12 => embedPair2542 corrSecondN02700MinusPointP012Rounded2575
  | 13 => embedPair2542 corrSecondN02700MinusPointP013Rounded2575
  | 14 => embedPair2542 corrSecondN02700MinusPointP014Rounded2575
  | 15 => embedPair2542 corrSecondN02700MinusPointP015Rounded2575
  | 16 => embedPair2542 corrSecondN02700MinusPointP016Rounded2575
  | 17 => embedPair2542 corrSecondN02700MinusPointP017Rounded2575
  | 18 => embedPair2542 corrSecondN02700MinusPointP018Rounded2575
  | 19 => embedPair2542 corrSecondN02700MinusPointP019Rounded2575
  | 20 => embedPair2542 corrSecondN02700MinusPointP020Rounded2575
  | 21 => embedPair2542 corrSecondN02700MinusPointP021Rounded2575
  | 22 => embedPair2542 corrSecondN02700MinusPointP022Rounded2575
  | 23 => embedPair2542 corrSecondN02700MinusPointP023Rounded2575
  | 24 => embedPair2542 corrSecondN02700MinusPointP024Rounded2575
  | 25 => embedPair2542 corrSecondN02700MinusPointP025Rounded2575
  | 26 => embedPair2542 corrSecondN02700MinusPointP026Rounded2575
  | 27 => embedPair2542 corrSecondN02700MinusPointP027Rounded2575
  | 28 => embedPair2542 corrSecondN02700MinusPointP028Rounded2575
  | 29 => embedPair2542 corrSecondN02700MinusPointP029Rounded2575
  | _ => 0

noncomputable def corrSecondN02700MinusSignedError2575 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => corrSecondN02700MinusPointP000Radius2575
  | 1 => corrSecondN02700MinusPointP001Radius2575
  | 2 => corrSecondN02700MinusPointP002Radius2575
  | 3 => corrSecondN02700MinusPointP003Radius2575
  | 4 => corrSecondN02700MinusPointP004Radius2575
  | 5 => corrSecondN02700MinusPointP005Radius2575
  | 6 => corrSecondN02700MinusPointP006Radius2575
  | 7 => corrSecondN02700MinusPointP007Radius2575
  | 8 => corrSecondN02700MinusPointP008Radius2575
  | 9 => corrSecondN02700MinusPointP009Radius2575
  | 10 => corrSecondN02700MinusPointP010Radius2575
  | 11 => corrSecondN02700MinusPointP011Radius2575
  | 12 => corrSecondN02700MinusPointP012Radius2575
  | 13 => corrSecondN02700MinusPointP013Radius2575
  | 14 => corrSecondN02700MinusPointP014Radius2575
  | 15 => corrSecondN02700MinusPointP015Radius2575
  | 16 => corrSecondN02700MinusPointP016Radius2575
  | 17 => corrSecondN02700MinusPointP017Radius2575
  | 18 => corrSecondN02700MinusPointP018Radius2575
  | 19 => corrSecondN02700MinusPointP019Radius2575
  | 20 => corrSecondN02700MinusPointP020Radius2575
  | 21 => corrSecondN02700MinusPointP021Radius2575
  | 22 => corrSecondN02700MinusPointP022Radius2575
  | 23 => corrSecondN02700MinusPointP023Radius2575
  | 24 => corrSecondN02700MinusPointP024Radius2575
  | 25 => corrSecondN02700MinusPointP025Radius2575
  | 26 => corrSecondN02700MinusPointP026Radius2575
  | 27 => corrSecondN02700MinusPointP027Radius2575
  | 28 => corrSecondN02700MinusPointP028Radius2575
  | 29 => corrSecondN02700MinusPointP029Radius2575
  | _ => 0

theorem corrSecondN02700MinusSignedExpError2575 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrSecondN02700MinusPointPosition2575 -
        corrSecondN02700MinusSignedValue2575 i‖ ≤ corrSecondN02700MinusSignedError2575 i := by
  fin_cases i
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP000RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP001RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP002RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP003RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP004RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP005RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP006RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP007RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP008RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP009RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP010RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP011RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP012RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP013RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP014RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP015RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP016RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP017RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP018RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP019RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP020RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP021RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP022RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP023RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP024RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP025RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP026RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP027RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP028RoundedError2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP029RoundedError2575

theorem corrSecondN02700MinusSignedUnitNorm2575 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrSecondN02700MinusPointPosition2575‖ ≤ 1
        := by
  fin_cases i
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP000DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP001DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP002DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP003DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP004DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP005DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP006DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP007DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP008DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP009DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP010DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP011DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP012DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP013DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP014DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP015DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP016DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP017DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP018DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP019DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP020DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP021DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP022DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP023DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP024DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP025DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP026DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP027DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP028DerivativeNorm2575
  · simpa only [corrSecondN02700MinusSignedValue2575, corrSecondN02700MinusSignedError2575] using
      corrSecondN02700MinusPointP029DerivativeNorm2575

noncomputable def corrSecondN02700MinusSignedSum2575 : ℂ := ⟨(((-(((4098573425992 * 10^40
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

noncomputable def corrSecondN02700MinusSignedUpper2575 : ℝ := ((1218308507 : ℝ) /
        50000000)

theorem corrSecondN02700MinusSignedSum_eq2575 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSecondN02700MinusSignedValue2575 i) =
      corrSecondN02700MinusSignedSum2575 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        corrSecondN02700MinusSignedValue2575,
      corrSecondN02700MinusSignedSum2575, embedPair2542,
          corrSecondN02700MinusPointP000Rounded2575,
      corrSecondN02700MinusPointP001Rounded2575,
      corrSecondN02700MinusPointP002Rounded2575,
      corrSecondN02700MinusPointP003Rounded2575,
      corrSecondN02700MinusPointP004Rounded2575,
      corrSecondN02700MinusPointP005Rounded2575,
      corrSecondN02700MinusPointP006Rounded2575,
      corrSecondN02700MinusPointP007Rounded2575,
      corrSecondN02700MinusPointP008Rounded2575,
      corrSecondN02700MinusPointP009Rounded2575,
      corrSecondN02700MinusPointP010Rounded2575,
      corrSecondN02700MinusPointP011Rounded2575,
      corrSecondN02700MinusPointP012Rounded2575,
      corrSecondN02700MinusPointP013Rounded2575,
      corrSecondN02700MinusPointP014Rounded2575,
      corrSecondN02700MinusPointP015Rounded2575,
      corrSecondN02700MinusPointP016Rounded2575,
      corrSecondN02700MinusPointP017Rounded2575,
      corrSecondN02700MinusPointP018Rounded2575,
      corrSecondN02700MinusPointP019Rounded2575,
      corrSecondN02700MinusPointP020Rounded2575,
      corrSecondN02700MinusPointP021Rounded2575,
      corrSecondN02700MinusPointP022Rounded2575,
      corrSecondN02700MinusPointP023Rounded2575,
      corrSecondN02700MinusPointP024Rounded2575,
      corrSecondN02700MinusPointP025Rounded2575,
      corrSecondN02700MinusPointP026Rounded2575,
      corrSecondN02700MinusPointP027Rounded2575,
      corrSecondN02700MinusPointP028Rounded2575,
      corrSecondN02700MinusPointP029Rounded2575, Complex.mul_re, Complex.mul_im]

theorem corrSecondN02700MinusSignedSum_norm2575 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSecondN02700MinusSignedValue2575 i‖ ≤
        ((609154251 :
        ℝ) /
        25000000) := by
  rw [corrSecondN02700MinusSignedSum_eq2575]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [corrSecondN02700MinusSignedSum2575]

theorem corrSecondN02700MinusSignedCharge2575 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * corrSecondN02700MinusSignedError2575 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      corrSecondN02700MinusSignedError2575, corrSecondN02700MinusPointP000Radius2575,
      corrSecondN02700MinusPointP001Radius2575,
      corrSecondN02700MinusPointP002Radius2575,
      corrSecondN02700MinusPointP003Radius2575,
      corrSecondN02700MinusPointP004Radius2575,
      corrSecondN02700MinusPointP005Radius2575,
      corrSecondN02700MinusPointP006Radius2575,
      corrSecondN02700MinusPointP007Radius2575,
      corrSecondN02700MinusPointP008Radius2575,
      corrSecondN02700MinusPointP009Radius2575,
      corrSecondN02700MinusPointP010Radius2575,
      corrSecondN02700MinusPointP011Radius2575,
      corrSecondN02700MinusPointP012Radius2575,
      corrSecondN02700MinusPointP013Radius2575,
      corrSecondN02700MinusPointP014Radius2575,
      corrSecondN02700MinusPointP015Radius2575,
      corrSecondN02700MinusPointP016Radius2575,
      corrSecondN02700MinusPointP017Radius2575,
      corrSecondN02700MinusPointP018Radius2575,
      corrSecondN02700MinusPointP019Radius2575,
      corrSecondN02700MinusPointP020Radius2575,
      corrSecondN02700MinusPointP021Radius2575,
      corrSecondN02700MinusPointP022Radius2575,
      corrSecondN02700MinusPointP023Radius2575,
      corrSecondN02700MinusPointP024Radius2575,
      corrSecondN02700MinusPointP025Radius2575,
      corrSecondN02700MinusPointP026Radius2575,
      corrSecondN02700MinusPointP027Radius2575,
      corrSecondN02700MinusPointP028Radius2575,
      corrSecondN02700MinusPointP029Radius2575]

theorem corrSecondN02700MinusSignedUpper_le2575 :
    signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 corrSecondN02700MinusPointPosition2575 ≤
          corrSecondN02700MinusSignedUpper2575 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrSecondN02700MinusPointPosition2575‖
            ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSecondN02700MinusSignedValue2575 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * corrSecondN02700MinusSignedError2575 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (corrSecondN02700MinusSignedExpError2575 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrSecondN02700MinusPointPosition2575‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (corrSecondN02700MinusSignedUnitNorm2575 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrSecondN02700MinusPointPosition2575‖)
          ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 corrSecondN02700MinusSignedUpper2575
  linarith [corrSecondN02700MinusSignedSum_norm2575, corrSecondN02700MinusSignedCharge2575]

theorem corrSecondN02700MinusPhysical2575 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        corrSecondN02700MinusPointPosition2575‖ ≤
      corrSecondN02700MinusSignedUpper2575 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        corrSecondN02700MinusPointPosition2575
  exact h.trans corrSecondN02700MinusSignedUpper_le2575

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrSecondN02700MinusSignedExpError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02700MinusSignedSum_eq2575
#print axioms ConnesWeilRH.Dev.corrSecondN02700MinusSignedCharge2575
#print axioms ConnesWeilRH.Dev.corrSecondN02700MinusSignedUpper_le2575
#print axioms ConnesWeilRH.Dev.corrSecondN02700MinusPhysical2575
