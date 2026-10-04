import ConnesWeilRH.Dev.C1RouteACorrSecondN02700PlusDerivatives2575
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem corrSecondN02700PlusPoint_triangle2575 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def corrSecondN02700PlusPointP000Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP000Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP000RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP000Factor2575
        corrSecondN02700PlusPointP000Center2575) =
        corrSecondN02700PlusPointP000Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP000RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP000Rounded2575‖ ≤
          corrSecondN02700PlusPointP000Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP000Factor2575
      corrSecondN02700PlusPointP000Center2575)
  rw [corrSecondN02700PlusPointP000RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP000Factor2575 * embedPair2542
        corrSecondN02700PlusPointP000Center2575)
    (embedPair2542 corrSecondN02700PlusPointP000Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP000DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP000Factor2575,
      corrSecondN02700PlusPointP000Error2575, rounding2542,
      corrSecondN02700PlusPointP000Radius2575]

theorem corrSecondN02700PlusPointP000DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP000Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP000RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP000Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP000Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP000Rounded2575]

def corrSecondN02700PlusPointP001Rounded2575 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP001Radius2575 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02700PlusPointP001RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP001Factor2575
        corrSecondN02700PlusPointP001Center2575) =
        corrSecondN02700PlusPointP001Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP001RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP001Rounded2575‖ ≤
          corrSecondN02700PlusPointP001Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP001Factor2575
      corrSecondN02700PlusPointP001Center2575)
  rw [corrSecondN02700PlusPointP001RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP001Factor2575 * embedPair2542
        corrSecondN02700PlusPointP001Center2575)
    (embedPair2542 corrSecondN02700PlusPointP001Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP001DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP001Factor2575,
      corrSecondN02700PlusPointP001Error2575, rounding2542,
      corrSecondN02700PlusPointP001Radius2575]

theorem corrSecondN02700PlusPointP001DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP001Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP001RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP001Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP001Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP001Rounded2575]

def corrSecondN02700PlusPointP002Rounded2575 : RatPair2542 :=
  (((319595 : ℚ) /
        316912650057057350374175801344),
    (((-1056677) : ℚ) /
        1267650600228229401496703205376))

noncomputable def corrSecondN02700PlusPointP002Radius2575 : ℝ := ((2199023262001 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02700PlusPointP002RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP002Factor2575
        corrSecondN02700PlusPointP002Center2575) =
        corrSecondN02700PlusPointP002Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP002RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP002Rounded2575‖ ≤
          corrSecondN02700PlusPointP002Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP002Factor2575
      corrSecondN02700PlusPointP002Center2575)
  rw [corrSecondN02700PlusPointP002RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP002Factor2575 * embedPair2542
        corrSecondN02700PlusPointP002Center2575)
    (embedPair2542 corrSecondN02700PlusPointP002Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP002DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP002Factor2575,
      corrSecondN02700PlusPointP002Error2575, rounding2542,
      corrSecondN02700PlusPointP002Radius2575]

theorem corrSecondN02700PlusPointP002DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP002Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP002RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP002Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP002Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP002Rounded2575]

def corrSecondN02700PlusPointP003Rounded2575 : RatPair2542 :=
  (((15395583093801 : ℚ) /
        1267650600228229401496703205376),
    ((3375515622365 : ℚ) /
        1267650600228229401496703205376))

noncomputable def corrSecondN02700PlusPointP003Radius2575 : ℝ := ((2276012570833 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02700PlusPointP003RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP003Factor2575
        corrSecondN02700PlusPointP003Center2575) =
        corrSecondN02700PlusPointP003Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP003RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP003Rounded2575‖ ≤
          corrSecondN02700PlusPointP003Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP003Factor2575
      corrSecondN02700PlusPointP003Center2575)
  rw [corrSecondN02700PlusPointP003RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP003Factor2575 * embedPair2542
        corrSecondN02700PlusPointP003Center2575)
    (embedPair2542 corrSecondN02700PlusPointP003Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP003DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP003Factor2575,
      corrSecondN02700PlusPointP003Error2575, rounding2542,
      corrSecondN02700PlusPointP003Radius2575]

theorem corrSecondN02700PlusPointP003DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP003Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP003RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP003Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP003Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP003Rounded2575]

def corrSecondN02700PlusPointP004Rounded2575 : RatPair2542 :=
  (((3081881776893327 : ℚ) /
        633825300114114700748351602688),
    (((-3768077214936263) : ℚ) /
        1267650600228229401496703205376))

noncomputable def corrSecondN02700PlusPointP004Radius2575 : ℝ := ((33988247501147 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02700PlusPointP004RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP004Factor2575
        corrSecondN02700PlusPointP004Center2575) =
        corrSecondN02700PlusPointP004Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP004RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP004Rounded2575‖ ≤
          corrSecondN02700PlusPointP004Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP004Factor2575
      corrSecondN02700PlusPointP004Center2575)
  rw [corrSecondN02700PlusPointP004RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP004Factor2575 * embedPair2542
        corrSecondN02700PlusPointP004Center2575)
    (embedPair2542 corrSecondN02700PlusPointP004Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP004DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP004Factor2575,
      corrSecondN02700PlusPointP004Error2575, rounding2542,
      corrSecondN02700PlusPointP004Radius2575]

theorem corrSecondN02700PlusPointP004DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP004Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP004RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP004Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP004Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP004Rounded2575]

def corrSecondN02700PlusPointP005Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP005Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP005RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP005Factor2575
        corrSecondN02700PlusPointP005Center2575) =
        corrSecondN02700PlusPointP005Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP005RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP005Rounded2575‖ ≤
          corrSecondN02700PlusPointP005Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP005Factor2575
      corrSecondN02700PlusPointP005Center2575)
  rw [corrSecondN02700PlusPointP005RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP005Factor2575 * embedPair2542
        corrSecondN02700PlusPointP005Center2575)
    (embedPair2542 corrSecondN02700PlusPointP005Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP005DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP005Factor2575,
      corrSecondN02700PlusPointP005Error2575, rounding2542,
      corrSecondN02700PlusPointP005Radius2575]

theorem corrSecondN02700PlusPointP005DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP005Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP005RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP005Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP005Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP005Rounded2575]

def corrSecondN02700PlusPointP006Rounded2575 : RatPair2542 :=
  (((3 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP006Radius2575 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02700PlusPointP006RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP006Factor2575
        corrSecondN02700PlusPointP006Center2575) =
        corrSecondN02700PlusPointP006Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP006RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP006Rounded2575‖ ≤
          corrSecondN02700PlusPointP006Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP006Factor2575
      corrSecondN02700PlusPointP006Center2575)
  rw [corrSecondN02700PlusPointP006RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP006Factor2575 * embedPair2542
        corrSecondN02700PlusPointP006Center2575)
    (embedPair2542 corrSecondN02700PlusPointP006Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP006DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP006Factor2575,
      corrSecondN02700PlusPointP006Error2575, rounding2542,
      corrSecondN02700PlusPointP006Radius2575]

theorem corrSecondN02700PlusPointP006DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP006Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP006RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP006Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP006Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP006Rounded2575]

def corrSecondN02700PlusPointP007Rounded2575 : RatPair2542 :=
  (((1837429076517 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP007Radius2575 : ℝ := ((2199290244015 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02700PlusPointP007RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP007Factor2575
        corrSecondN02700PlusPointP007Center2575) =
        corrSecondN02700PlusPointP007Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP007RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP007Rounded2575‖ ≤
          corrSecondN02700PlusPointP007Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP007Factor2575
      corrSecondN02700PlusPointP007Center2575)
  rw [corrSecondN02700PlusPointP007RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP007Factor2575 * embedPair2542
        corrSecondN02700PlusPointP007Center2575)
    (embedPair2542 corrSecondN02700PlusPointP007Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP007DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP007Factor2575,
      corrSecondN02700PlusPointP007Error2575, rounding2542,
      corrSecondN02700PlusPointP007Radius2575]

theorem corrSecondN02700PlusPointP007DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP007Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP007RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP007Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP007Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP007Rounded2575]

def corrSecondN02700PlusPointP008Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP008Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP008RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP008Factor2575
        corrSecondN02700PlusPointP008Center2575) =
        corrSecondN02700PlusPointP008Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP008RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP008Rounded2575‖ ≤
          corrSecondN02700PlusPointP008Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP008Factor2575
      corrSecondN02700PlusPointP008Center2575)
  rw [corrSecondN02700PlusPointP008RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP008Factor2575 * embedPair2542
        corrSecondN02700PlusPointP008Center2575)
    (embedPair2542 corrSecondN02700PlusPointP008Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP008DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP008Factor2575,
      corrSecondN02700PlusPointP008Error2575, rounding2542,
      corrSecondN02700PlusPointP008Radius2575]

theorem corrSecondN02700PlusPointP008DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP008Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP008RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP008Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP008Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP008Rounded2575]

def corrSecondN02700PlusPointP009Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP009Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP009RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP009Factor2575
        corrSecondN02700PlusPointP009Center2575) =
        corrSecondN02700PlusPointP009Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP009RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP009Rounded2575‖ ≤
          corrSecondN02700PlusPointP009Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP009Factor2575
      corrSecondN02700PlusPointP009Center2575)
  rw [corrSecondN02700PlusPointP009RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP009Factor2575 * embedPair2542
        corrSecondN02700PlusPointP009Center2575)
    (embedPair2542 corrSecondN02700PlusPointP009Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP009DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP009Factor2575,
      corrSecondN02700PlusPointP009Error2575, rounding2542,
      corrSecondN02700PlusPointP009Radius2575]

theorem corrSecondN02700PlusPointP009DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP009Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP009RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP009Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP009Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP009Rounded2575]

def corrSecondN02700PlusPointP010Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP010Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP010RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP010Factor2575
        corrSecondN02700PlusPointP010Center2575) =
        corrSecondN02700PlusPointP010Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP010RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP010Rounded2575‖ ≤
          corrSecondN02700PlusPointP010Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP010Factor2575
      corrSecondN02700PlusPointP010Center2575)
  rw [corrSecondN02700PlusPointP010RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP010Factor2575 * embedPair2542
        corrSecondN02700PlusPointP010Center2575)
    (embedPair2542 corrSecondN02700PlusPointP010Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP010DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP010Factor2575,
      corrSecondN02700PlusPointP010Error2575, rounding2542,
      corrSecondN02700PlusPointP010Radius2575]

theorem corrSecondN02700PlusPointP010DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP010Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP010RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP010Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP010Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP010Rounded2575]

def corrSecondN02700PlusPointP011Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP011Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP011RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP011Factor2575
        corrSecondN02700PlusPointP011Center2575) =
        corrSecondN02700PlusPointP011Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP011RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP011Rounded2575‖ ≤
          corrSecondN02700PlusPointP011Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP011Factor2575
      corrSecondN02700PlusPointP011Center2575)
  rw [corrSecondN02700PlusPointP011RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP011Factor2575 * embedPair2542
        corrSecondN02700PlusPointP011Center2575)
    (embedPair2542 corrSecondN02700PlusPointP011Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP011DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP011Factor2575,
      corrSecondN02700PlusPointP011Error2575, rounding2542,
      corrSecondN02700PlusPointP011Radius2575]

theorem corrSecondN02700PlusPointP011DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP011Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP011RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP011Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP011Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP011Rounded2575]

def corrSecondN02700PlusPointP012Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP012Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP012RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP012Factor2575
        corrSecondN02700PlusPointP012Center2575) =
        corrSecondN02700PlusPointP012Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP012RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP012Rounded2575‖ ≤
          corrSecondN02700PlusPointP012Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP012Factor2575
      corrSecondN02700PlusPointP012Center2575)
  rw [corrSecondN02700PlusPointP012RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP012Factor2575 * embedPair2542
        corrSecondN02700PlusPointP012Center2575)
    (embedPair2542 corrSecondN02700PlusPointP012Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP012DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP012Factor2575,
      corrSecondN02700PlusPointP012Error2575, rounding2542,
      corrSecondN02700PlusPointP012Radius2575]

theorem corrSecondN02700PlusPointP012DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP012Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP012RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP012Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP012Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP012Rounded2575]

def corrSecondN02700PlusPointP013Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP013Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP013RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP013Factor2575
        corrSecondN02700PlusPointP013Center2575) =
        corrSecondN02700PlusPointP013Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP013RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP013Rounded2575‖ ≤
          corrSecondN02700PlusPointP013Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP013Factor2575
      corrSecondN02700PlusPointP013Center2575)
  rw [corrSecondN02700PlusPointP013RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP013Factor2575 * embedPair2542
        corrSecondN02700PlusPointP013Center2575)
    (embedPair2542 corrSecondN02700PlusPointP013Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP013DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP013Factor2575,
      corrSecondN02700PlusPointP013Error2575, rounding2542,
      corrSecondN02700PlusPointP013Radius2575]

theorem corrSecondN02700PlusPointP013DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP013Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP013RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP013Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP013Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP013Rounded2575]

def corrSecondN02700PlusPointP014Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP014Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP014RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP014Factor2575
        corrSecondN02700PlusPointP014Center2575) =
        corrSecondN02700PlusPointP014Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP014RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP014Rounded2575‖ ≤
          corrSecondN02700PlusPointP014Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP014Factor2575
      corrSecondN02700PlusPointP014Center2575)
  rw [corrSecondN02700PlusPointP014RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP014Factor2575 * embedPair2542
        corrSecondN02700PlusPointP014Center2575)
    (embedPair2542 corrSecondN02700PlusPointP014Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP014DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP014Factor2575,
      corrSecondN02700PlusPointP014Error2575, rounding2542,
      corrSecondN02700PlusPointP014Radius2575]

theorem corrSecondN02700PlusPointP014DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP014Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP014RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP014Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP014Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP014Rounded2575]

def corrSecondN02700PlusPointP015Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP015Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP015RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP015Factor2575
        corrSecondN02700PlusPointP015Center2575) =
        corrSecondN02700PlusPointP015Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP015RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP015Rounded2575‖ ≤
          corrSecondN02700PlusPointP015Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP015Factor2575
      corrSecondN02700PlusPointP015Center2575)
  rw [corrSecondN02700PlusPointP015RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP015Factor2575 * embedPair2542
        corrSecondN02700PlusPointP015Center2575)
    (embedPair2542 corrSecondN02700PlusPointP015Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP015DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP015Factor2575,
      corrSecondN02700PlusPointP015Error2575, rounding2542,
      corrSecondN02700PlusPointP015Radius2575]

theorem corrSecondN02700PlusPointP015DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP015Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP015RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP015Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP015Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP015Rounded2575]

def corrSecondN02700PlusPointP016Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP016Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP016RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP016Factor2575
        corrSecondN02700PlusPointP016Center2575) =
        corrSecondN02700PlusPointP016Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP016RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP016Rounded2575‖ ≤
          corrSecondN02700PlusPointP016Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP016Factor2575
      corrSecondN02700PlusPointP016Center2575)
  rw [corrSecondN02700PlusPointP016RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP016Factor2575 * embedPair2542
        corrSecondN02700PlusPointP016Center2575)
    (embedPair2542 corrSecondN02700PlusPointP016Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP016DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP016Factor2575,
      corrSecondN02700PlusPointP016Error2575, rounding2542,
      corrSecondN02700PlusPointP016Radius2575]

theorem corrSecondN02700PlusPointP016DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP016Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP016RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP016Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP016Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP016Rounded2575]

def corrSecondN02700PlusPointP017Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP017Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP017RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP017Factor2575
        corrSecondN02700PlusPointP017Center2575) =
        corrSecondN02700PlusPointP017Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP017RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP017Rounded2575‖ ≤
          corrSecondN02700PlusPointP017Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP017Factor2575
      corrSecondN02700PlusPointP017Center2575)
  rw [corrSecondN02700PlusPointP017RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP017Factor2575 * embedPair2542
        corrSecondN02700PlusPointP017Center2575)
    (embedPair2542 corrSecondN02700PlusPointP017Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP017DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP017Factor2575,
      corrSecondN02700PlusPointP017Error2575, rounding2542,
      corrSecondN02700PlusPointP017Radius2575]

theorem corrSecondN02700PlusPointP017DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP017Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP017RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP017Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP017Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP017Rounded2575]

def corrSecondN02700PlusPointP018Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP018Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP018RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP018Factor2575
        corrSecondN02700PlusPointP018Center2575) =
        corrSecondN02700PlusPointP018Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP018RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP018Rounded2575‖ ≤
          corrSecondN02700PlusPointP018Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP018Factor2575
      corrSecondN02700PlusPointP018Center2575)
  rw [corrSecondN02700PlusPointP018RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP018Factor2575 * embedPair2542
        corrSecondN02700PlusPointP018Center2575)
    (embedPair2542 corrSecondN02700PlusPointP018Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP018DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP018Factor2575,
      corrSecondN02700PlusPointP018Error2575, rounding2542,
      corrSecondN02700PlusPointP018Radius2575]

theorem corrSecondN02700PlusPointP018DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP018Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP018RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP018Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP018Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP018Rounded2575]

def corrSecondN02700PlusPointP019Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP019Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP019RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP019Factor2575
        corrSecondN02700PlusPointP019Center2575) =
        corrSecondN02700PlusPointP019Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP019RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP019Rounded2575‖ ≤
          corrSecondN02700PlusPointP019Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP019Factor2575
      corrSecondN02700PlusPointP019Center2575)
  rw [corrSecondN02700PlusPointP019RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP019Factor2575 * embedPair2542
        corrSecondN02700PlusPointP019Center2575)
    (embedPair2542 corrSecondN02700PlusPointP019Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP019DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP019Factor2575,
      corrSecondN02700PlusPointP019Error2575, rounding2542,
      corrSecondN02700PlusPointP019Radius2575]

theorem corrSecondN02700PlusPointP019DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP019Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP019RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP019Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP019Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP019Rounded2575]

def corrSecondN02700PlusPointP020Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP020Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP020RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP020Factor2575
        corrSecondN02700PlusPointP020Center2575) =
        corrSecondN02700PlusPointP020Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP020RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP020Rounded2575‖ ≤
          corrSecondN02700PlusPointP020Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP020Factor2575
      corrSecondN02700PlusPointP020Center2575)
  rw [corrSecondN02700PlusPointP020RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP020Factor2575 * embedPair2542
        corrSecondN02700PlusPointP020Center2575)
    (embedPair2542 corrSecondN02700PlusPointP020Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP020DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP020Factor2575,
      corrSecondN02700PlusPointP020Error2575, rounding2542,
      corrSecondN02700PlusPointP020Radius2575]

theorem corrSecondN02700PlusPointP020DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP020Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP020RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP020Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP020Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP020Rounded2575]

def corrSecondN02700PlusPointP021Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP021Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP021RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP021Factor2575
        corrSecondN02700PlusPointP021Center2575) =
        corrSecondN02700PlusPointP021Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP021RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP021Rounded2575‖ ≤
          corrSecondN02700PlusPointP021Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP021Factor2575
      corrSecondN02700PlusPointP021Center2575)
  rw [corrSecondN02700PlusPointP021RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP021Factor2575 * embedPair2542
        corrSecondN02700PlusPointP021Center2575)
    (embedPair2542 corrSecondN02700PlusPointP021Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP021DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP021Factor2575,
      corrSecondN02700PlusPointP021Error2575, rounding2542,
      corrSecondN02700PlusPointP021Radius2575]

theorem corrSecondN02700PlusPointP021DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP021Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP021RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP021Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP021Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP021Rounded2575]

def corrSecondN02700PlusPointP022Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP022Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP022RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP022Factor2575
        corrSecondN02700PlusPointP022Center2575) =
        corrSecondN02700PlusPointP022Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP022RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP022Rounded2575‖ ≤
          corrSecondN02700PlusPointP022Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP022Factor2575
      corrSecondN02700PlusPointP022Center2575)
  rw [corrSecondN02700PlusPointP022RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP022Factor2575 * embedPair2542
        corrSecondN02700PlusPointP022Center2575)
    (embedPair2542 corrSecondN02700PlusPointP022Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP022DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP022Factor2575,
      corrSecondN02700PlusPointP022Error2575, rounding2542,
      corrSecondN02700PlusPointP022Radius2575]

theorem corrSecondN02700PlusPointP022DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP022Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP022RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP022Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP022Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP022Rounded2575]

def corrSecondN02700PlusPointP023Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP023Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP023RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP023Factor2575
        corrSecondN02700PlusPointP023Center2575) =
        corrSecondN02700PlusPointP023Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP023RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP023Rounded2575‖ ≤
          corrSecondN02700PlusPointP023Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP023Factor2575
      corrSecondN02700PlusPointP023Center2575)
  rw [corrSecondN02700PlusPointP023RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP023Factor2575 * embedPair2542
        corrSecondN02700PlusPointP023Center2575)
    (embedPair2542 corrSecondN02700PlusPointP023Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP023DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP023Factor2575,
      corrSecondN02700PlusPointP023Error2575, rounding2542,
      corrSecondN02700PlusPointP023Radius2575]

theorem corrSecondN02700PlusPointP023DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP023Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP023RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP023Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP023Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP023Rounded2575]

def corrSecondN02700PlusPointP024Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP024Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP024RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP024Factor2575
        corrSecondN02700PlusPointP024Center2575) =
        corrSecondN02700PlusPointP024Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP024RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP024Rounded2575‖ ≤
          corrSecondN02700PlusPointP024Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP024Factor2575
      corrSecondN02700PlusPointP024Center2575)
  rw [corrSecondN02700PlusPointP024RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP024Factor2575 * embedPair2542
        corrSecondN02700PlusPointP024Center2575)
    (embedPair2542 corrSecondN02700PlusPointP024Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP024DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP024Factor2575,
      corrSecondN02700PlusPointP024Error2575, rounding2542,
      corrSecondN02700PlusPointP024Radius2575]

theorem corrSecondN02700PlusPointP024DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP024Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP024RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP024Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP024Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP024Rounded2575]

def corrSecondN02700PlusPointP025Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP025Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP025RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP025Factor2575
        corrSecondN02700PlusPointP025Center2575) =
        corrSecondN02700PlusPointP025Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP025RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP025Rounded2575‖ ≤
          corrSecondN02700PlusPointP025Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP025Factor2575
      corrSecondN02700PlusPointP025Center2575)
  rw [corrSecondN02700PlusPointP025RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP025Factor2575 * embedPair2542
        corrSecondN02700PlusPointP025Center2575)
    (embedPair2542 corrSecondN02700PlusPointP025Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP025DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP025Factor2575,
      corrSecondN02700PlusPointP025Error2575, rounding2542,
      corrSecondN02700PlusPointP025Radius2575]

theorem corrSecondN02700PlusPointP025DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP025Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP025RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP025Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP025Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP025Rounded2575]

def corrSecondN02700PlusPointP026Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP026Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP026RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP026Factor2575
        corrSecondN02700PlusPointP026Center2575) =
        corrSecondN02700PlusPointP026Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP026RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP026Rounded2575‖ ≤
          corrSecondN02700PlusPointP026Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP026Factor2575
      corrSecondN02700PlusPointP026Center2575)
  rw [corrSecondN02700PlusPointP026RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP026Factor2575 * embedPair2542
        corrSecondN02700PlusPointP026Center2575)
    (embedPair2542 corrSecondN02700PlusPointP026Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP026DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP026Factor2575,
      corrSecondN02700PlusPointP026Error2575, rounding2542,
      corrSecondN02700PlusPointP026Radius2575]

theorem corrSecondN02700PlusPointP026DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP026Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP026RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP026Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP026Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP026Rounded2575]

def corrSecondN02700PlusPointP027Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP027Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP027RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP027Factor2575
        corrSecondN02700PlusPointP027Center2575) =
        corrSecondN02700PlusPointP027Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP027RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP027Rounded2575‖ ≤
          corrSecondN02700PlusPointP027Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP027Factor2575
      corrSecondN02700PlusPointP027Center2575)
  rw [corrSecondN02700PlusPointP027RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP027Factor2575 * embedPair2542
        corrSecondN02700PlusPointP027Center2575)
    (embedPair2542 corrSecondN02700PlusPointP027Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP027DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP027Factor2575,
      corrSecondN02700PlusPointP027Error2575, rounding2542,
      corrSecondN02700PlusPointP027Radius2575]

theorem corrSecondN02700PlusPointP027DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP027Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP027RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP027Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP027Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP027Rounded2575]

def corrSecondN02700PlusPointP028Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP028Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP028RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP028Factor2575
        corrSecondN02700PlusPointP028Center2575) =
        corrSecondN02700PlusPointP028Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP028RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP028Rounded2575‖ ≤
          corrSecondN02700PlusPointP028Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP028Factor2575
      corrSecondN02700PlusPointP028Center2575)
  rw [corrSecondN02700PlusPointP028RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP028Factor2575 * embedPair2542
        corrSecondN02700PlusPointP028Center2575)
    (embedPair2542 corrSecondN02700PlusPointP028Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP028DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP028Factor2575,
      corrSecondN02700PlusPointP028Error2575, rounding2542,
      corrSecondN02700PlusPointP028Radius2575]

theorem corrSecondN02700PlusPointP028DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP028Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP028RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP028Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP028Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP028Rounded2575]

def corrSecondN02700PlusPointP029Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02700PlusPointP029Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02700PlusPointP029RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02700PlusPointP029Factor2575
        corrSecondN02700PlusPointP029Center2575) =
        corrSecondN02700PlusPointP029Rounded2575 := by
  cbv

theorem corrSecondN02700PlusPointP029RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02700PlusPointPosition2575 -
      embedPair2542 corrSecondN02700PlusPointP029Rounded2575‖ ≤
          corrSecondN02700PlusPointP029Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02700PlusPointP029Factor2575
      corrSecondN02700PlusPointP029Center2575)
  rw [corrSecondN02700PlusPointP029RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP029Factor2575 * embedPair2542
        corrSecondN02700PlusPointP029Center2575)
    (embedPair2542 corrSecondN02700PlusPointP029Rounded2575)).trans (add_le_add
        corrSecondN02700PlusPointP029DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02700PlusPointP029Factor2575,
      corrSecondN02700PlusPointP029Error2575, rounding2542,
      corrSecondN02700PlusPointP029Radius2575]

theorem corrSecondN02700PlusPointP029DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02700PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02700PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02700PlusPointPosition2575)
    (embedPair2542 corrSecondN02700PlusPointP029Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02700PlusPointP029RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02700PlusPointP029Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02700PlusPointP029Radius2575, pairMagnitude2542,
      corrSecondN02700PlusPointP029Rounded2575]

noncomputable def corrSecondN02700PlusSignedValue2575 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 corrSecondN02700PlusPointP000Rounded2575
  | 1 => embedPair2542 corrSecondN02700PlusPointP001Rounded2575
  | 2 => embedPair2542 corrSecondN02700PlusPointP002Rounded2575
  | 3 => embedPair2542 corrSecondN02700PlusPointP003Rounded2575
  | 4 => embedPair2542 corrSecondN02700PlusPointP004Rounded2575
  | 5 => embedPair2542 corrSecondN02700PlusPointP005Rounded2575
  | 6 => embedPair2542 corrSecondN02700PlusPointP006Rounded2575
  | 7 => embedPair2542 corrSecondN02700PlusPointP007Rounded2575
  | 8 => embedPair2542 corrSecondN02700PlusPointP008Rounded2575
  | 9 => embedPair2542 corrSecondN02700PlusPointP009Rounded2575
  | 10 => embedPair2542 corrSecondN02700PlusPointP010Rounded2575
  | 11 => embedPair2542 corrSecondN02700PlusPointP011Rounded2575
  | 12 => embedPair2542 corrSecondN02700PlusPointP012Rounded2575
  | 13 => embedPair2542 corrSecondN02700PlusPointP013Rounded2575
  | 14 => embedPair2542 corrSecondN02700PlusPointP014Rounded2575
  | 15 => embedPair2542 corrSecondN02700PlusPointP015Rounded2575
  | 16 => embedPair2542 corrSecondN02700PlusPointP016Rounded2575
  | 17 => embedPair2542 corrSecondN02700PlusPointP017Rounded2575
  | 18 => embedPair2542 corrSecondN02700PlusPointP018Rounded2575
  | 19 => embedPair2542 corrSecondN02700PlusPointP019Rounded2575
  | 20 => embedPair2542 corrSecondN02700PlusPointP020Rounded2575
  | 21 => embedPair2542 corrSecondN02700PlusPointP021Rounded2575
  | 22 => embedPair2542 corrSecondN02700PlusPointP022Rounded2575
  | 23 => embedPair2542 corrSecondN02700PlusPointP023Rounded2575
  | 24 => embedPair2542 corrSecondN02700PlusPointP024Rounded2575
  | 25 => embedPair2542 corrSecondN02700PlusPointP025Rounded2575
  | 26 => embedPair2542 corrSecondN02700PlusPointP026Rounded2575
  | 27 => embedPair2542 corrSecondN02700PlusPointP027Rounded2575
  | 28 => embedPair2542 corrSecondN02700PlusPointP028Rounded2575
  | 29 => embedPair2542 corrSecondN02700PlusPointP029Rounded2575
  | _ => 0

noncomputable def corrSecondN02700PlusSignedError2575 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => corrSecondN02700PlusPointP000Radius2575
  | 1 => corrSecondN02700PlusPointP001Radius2575
  | 2 => corrSecondN02700PlusPointP002Radius2575
  | 3 => corrSecondN02700PlusPointP003Radius2575
  | 4 => corrSecondN02700PlusPointP004Radius2575
  | 5 => corrSecondN02700PlusPointP005Radius2575
  | 6 => corrSecondN02700PlusPointP006Radius2575
  | 7 => corrSecondN02700PlusPointP007Radius2575
  | 8 => corrSecondN02700PlusPointP008Radius2575
  | 9 => corrSecondN02700PlusPointP009Radius2575
  | 10 => corrSecondN02700PlusPointP010Radius2575
  | 11 => corrSecondN02700PlusPointP011Radius2575
  | 12 => corrSecondN02700PlusPointP012Radius2575
  | 13 => corrSecondN02700PlusPointP013Radius2575
  | 14 => corrSecondN02700PlusPointP014Radius2575
  | 15 => corrSecondN02700PlusPointP015Radius2575
  | 16 => corrSecondN02700PlusPointP016Radius2575
  | 17 => corrSecondN02700PlusPointP017Radius2575
  | 18 => corrSecondN02700PlusPointP018Radius2575
  | 19 => corrSecondN02700PlusPointP019Radius2575
  | 20 => corrSecondN02700PlusPointP020Radius2575
  | 21 => corrSecondN02700PlusPointP021Radius2575
  | 22 => corrSecondN02700PlusPointP022Radius2575
  | 23 => corrSecondN02700PlusPointP023Radius2575
  | 24 => corrSecondN02700PlusPointP024Radius2575
  | 25 => corrSecondN02700PlusPointP025Radius2575
  | 26 => corrSecondN02700PlusPointP026Radius2575
  | 27 => corrSecondN02700PlusPointP027Radius2575
  | 28 => corrSecondN02700PlusPointP028Radius2575
  | 29 => corrSecondN02700PlusPointP029Radius2575
  | _ => 0

theorem corrSecondN02700PlusSignedExpError2575 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrSecondN02700PlusPointPosition2575 -
        corrSecondN02700PlusSignedValue2575 i‖ ≤ corrSecondN02700PlusSignedError2575 i := by
  fin_cases i
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP000RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP001RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP002RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP003RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP004RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP005RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP006RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP007RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP008RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP009RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP010RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP011RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP012RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP013RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP014RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP015RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP016RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP017RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP018RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP019RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP020RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP021RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP022RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP023RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP024RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP025RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP026RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP027RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP028RoundedError2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP029RoundedError2575

theorem corrSecondN02700PlusSignedUnitNorm2575 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrSecondN02700PlusPointPosition2575‖ ≤ 1
        := by
  fin_cases i
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP000DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP001DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP002DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP003DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP004DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP005DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP006DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP007DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP008DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP009DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP010DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP011DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP012DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP013DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP014DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP015DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP016DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP017DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP018DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP019DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP020DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP021DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP022DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP023DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP024DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP025DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP026DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP027DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP028DerivativeNorm2575
  · simpa only [corrSecondN02700PlusSignedValue2575, corrSecondN02700PlusSignedError2575] using
      corrSecondN02700PlusPointP029DerivativeNorm2575

noncomputable def corrSecondN02700PlusSignedSum2575 : ℂ := ⟨(((-(((758399844469 * 10^40
        + 6704244910445264267748108629138308076368) * 10^40
        + 436671977840797100341221016888902709944) * 10^40
        + 7871525491157729545921025069384405364453)) : ℝ) /
        (((709803441694 * 10^40
        + 9286040520740311406294280797278912962090) * 10^40
        + 4324364277263734305479824015949823344796) * 10^40
        + 2659731992932150006119314388217384402944)),
    (((((427990524722 * 10^40
        + 9953529228440023167029319906415705308102) * 10^40
        + 4829843721194745457553512532188370322280) * 10^40
        + 9052091824211602140353261287733858410759) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888))⟩

noncomputable def corrSecondN02700PlusSignedUpper2575 : ℝ := ((55509237 : ℝ) /
        50000000)

theorem corrSecondN02700PlusSignedSum_eq2575 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSecondN02700PlusSignedValue2575 i) =
      corrSecondN02700PlusSignedSum2575 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        corrSecondN02700PlusSignedValue2575,
      corrSecondN02700PlusSignedSum2575, embedPair2542, corrSecondN02700PlusPointP000Rounded2575,
      corrSecondN02700PlusPointP001Rounded2575,
      corrSecondN02700PlusPointP002Rounded2575,
      corrSecondN02700PlusPointP003Rounded2575,
      corrSecondN02700PlusPointP004Rounded2575,
      corrSecondN02700PlusPointP005Rounded2575,
      corrSecondN02700PlusPointP006Rounded2575,
      corrSecondN02700PlusPointP007Rounded2575,
      corrSecondN02700PlusPointP008Rounded2575,
      corrSecondN02700PlusPointP009Rounded2575,
      corrSecondN02700PlusPointP010Rounded2575,
      corrSecondN02700PlusPointP011Rounded2575,
      corrSecondN02700PlusPointP012Rounded2575,
      corrSecondN02700PlusPointP013Rounded2575,
      corrSecondN02700PlusPointP014Rounded2575,
      corrSecondN02700PlusPointP015Rounded2575,
      corrSecondN02700PlusPointP016Rounded2575,
      corrSecondN02700PlusPointP017Rounded2575,
      corrSecondN02700PlusPointP018Rounded2575,
      corrSecondN02700PlusPointP019Rounded2575,
      corrSecondN02700PlusPointP020Rounded2575,
      corrSecondN02700PlusPointP021Rounded2575,
      corrSecondN02700PlusPointP022Rounded2575,
      corrSecondN02700PlusPointP023Rounded2575,
      corrSecondN02700PlusPointP024Rounded2575,
      corrSecondN02700PlusPointP025Rounded2575,
      corrSecondN02700PlusPointP026Rounded2575,
      corrSecondN02700PlusPointP027Rounded2575,
      corrSecondN02700PlusPointP028Rounded2575,
      corrSecondN02700PlusPointP029Rounded2575, Complex.mul_re, Complex.mul_im]

theorem corrSecondN02700PlusSignedSum_norm2575 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSecondN02700PlusSignedValue2575 i‖ ≤
        ((3469327 : ℝ)
        /
        3125000) := by
  rw [corrSecondN02700PlusSignedSum_eq2575]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [corrSecondN02700PlusSignedSum2575]

theorem corrSecondN02700PlusSignedCharge2575 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * corrSecondN02700PlusSignedError2575 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      corrSecondN02700PlusSignedError2575, corrSecondN02700PlusPointP000Radius2575,
      corrSecondN02700PlusPointP001Radius2575,
      corrSecondN02700PlusPointP002Radius2575,
      corrSecondN02700PlusPointP003Radius2575,
      corrSecondN02700PlusPointP004Radius2575,
      corrSecondN02700PlusPointP005Radius2575,
      corrSecondN02700PlusPointP006Radius2575,
      corrSecondN02700PlusPointP007Radius2575,
      corrSecondN02700PlusPointP008Radius2575,
      corrSecondN02700PlusPointP009Radius2575,
      corrSecondN02700PlusPointP010Radius2575,
      corrSecondN02700PlusPointP011Radius2575,
      corrSecondN02700PlusPointP012Radius2575,
      corrSecondN02700PlusPointP013Radius2575,
      corrSecondN02700PlusPointP014Radius2575,
      corrSecondN02700PlusPointP015Radius2575,
      corrSecondN02700PlusPointP016Radius2575,
      corrSecondN02700PlusPointP017Radius2575,
      corrSecondN02700PlusPointP018Radius2575,
      corrSecondN02700PlusPointP019Radius2575,
      corrSecondN02700PlusPointP020Radius2575,
      corrSecondN02700PlusPointP021Radius2575,
      corrSecondN02700PlusPointP022Radius2575,
      corrSecondN02700PlusPointP023Radius2575,
      corrSecondN02700PlusPointP024Radius2575,
      corrSecondN02700PlusPointP025Radius2575,
      corrSecondN02700PlusPointP026Radius2575,
      corrSecondN02700PlusPointP027Radius2575,
      corrSecondN02700PlusPointP028Radius2575,
      corrSecondN02700PlusPointP029Radius2575]

theorem corrSecondN02700PlusSignedUpper_le2575 :
    signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 corrSecondN02700PlusPointPosition2575 ≤
          corrSecondN02700PlusSignedUpper2575 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrSecondN02700PlusPointPosition2575‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSecondN02700PlusSignedValue2575 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * corrSecondN02700PlusSignedError2575 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (corrSecondN02700PlusSignedExpError2575
        i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrSecondN02700PlusPointPosition2575‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (corrSecondN02700PlusSignedUnitNorm2575 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrSecondN02700PlusPointPosition2575‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 corrSecondN02700PlusSignedUpper2575
  linarith [corrSecondN02700PlusSignedSum_norm2575, corrSecondN02700PlusSignedCharge2575]

theorem corrSecondN02700PlusPhysical2575 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        corrSecondN02700PlusPointPosition2575‖ ≤
      corrSecondN02700PlusSignedUpper2575 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        corrSecondN02700PlusPointPosition2575
  exact h.trans corrSecondN02700PlusSignedUpper_le2575

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrSecondN02700PlusSignedExpError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02700PlusSignedSum_eq2575
#print axioms ConnesWeilRH.Dev.corrSecondN02700PlusSignedCharge2575
#print axioms ConnesWeilRH.Dev.corrSecondN02700PlusSignedUpper_le2575
#print axioms ConnesWeilRH.Dev.corrSecondN02700PlusPhysical2575
