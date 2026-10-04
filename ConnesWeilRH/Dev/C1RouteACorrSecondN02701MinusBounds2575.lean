import ConnesWeilRH.Dev.C1RouteACorrSecondN02701MinusDerivatives2575
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem corrSecondN02701MinusPoint_triangle2575 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def corrSecondN02701MinusPointP000Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP000Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02701MinusPointP000RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP000Factor2575
        corrSecondN02701MinusPointP000Center2575) =
        corrSecondN02701MinusPointP000Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP000RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP000Rounded2575‖ ≤
          corrSecondN02701MinusPointP000Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP000Factor2575
      corrSecondN02701MinusPointP000Center2575)
  rw [corrSecondN02701MinusPointP000RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP000Factor2575 * embedPair2542
        corrSecondN02701MinusPointP000Center2575)
    (embedPair2542 corrSecondN02701MinusPointP000Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP000DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP000Factor2575,
      corrSecondN02701MinusPointP000Error2575, rounding2542,
      corrSecondN02701MinusPointP000Radius2575]

theorem corrSecondN02701MinusPointP000DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP000Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP000RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP000Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP000Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP000Rounded2575]

def corrSecondN02701MinusPointP001Rounded2575 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP001Radius2575 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701MinusPointP001RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP001Factor2575
        corrSecondN02701MinusPointP001Center2575) =
        corrSecondN02701MinusPointP001Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP001RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP001Rounded2575‖ ≤
          corrSecondN02701MinusPointP001Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP001Factor2575
      corrSecondN02701MinusPointP001Center2575)
  rw [corrSecondN02701MinusPointP001RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP001Factor2575 * embedPair2542
        corrSecondN02701MinusPointP001Center2575)
    (embedPair2542 corrSecondN02701MinusPointP001Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP001DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP001Factor2575,
      corrSecondN02701MinusPointP001Error2575, rounding2542,
      corrSecondN02701MinusPointP001Radius2575]

theorem corrSecondN02701MinusPointP001DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP001Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP001RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP001Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP001Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP001Rounded2575]

def corrSecondN02701MinusPointP002Rounded2575 : RatPair2542 :=
  (((30801705 : ℚ) /
        1267650600228229401496703205376),
    (((-21706931) : ℚ) /
        1267650600228229401496703205376))

noncomputable def corrSecondN02701MinusPointP002Radius2575 : ℝ := ((2199023397881 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701MinusPointP002RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP002Factor2575
        corrSecondN02701MinusPointP002Center2575) =
        corrSecondN02701MinusPointP002Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP002RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP002Rounded2575‖ ≤
          corrSecondN02701MinusPointP002Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP002Factor2575
      corrSecondN02701MinusPointP002Center2575)
  rw [corrSecondN02701MinusPointP002RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP002Factor2575 * embedPair2542
        corrSecondN02701MinusPointP002Center2575)
    (embedPair2542 corrSecondN02701MinusPointP002Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP002DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP002Factor2575,
      corrSecondN02701MinusPointP002Error2575, rounding2542,
      corrSecondN02701MinusPointP002Radius2575]

theorem corrSecondN02701MinusPointP002DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP002Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP002RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP002Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP002Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP002Rounded2575]

def corrSecondN02701MinusPointP003Rounded2575 : RatPair2542 :=
  (((332658606788883 : ℚ) /
        1267650600228229401496703205376),
    ((26789416028431 : ℚ) /
        316912650057057350374175801344))

noncomputable def corrSecondN02701MinusPointP003Radius2575 : ℝ := ((243242258949 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem corrSecondN02701MinusPointP003RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP003Factor2575
        corrSecondN02701MinusPointP003Center2575) =
        corrSecondN02701MinusPointP003Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP003RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP003Rounded2575‖ ≤
          corrSecondN02701MinusPointP003Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP003Factor2575
      corrSecondN02701MinusPointP003Center2575)
  rw [corrSecondN02701MinusPointP003RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP003Factor2575 * embedPair2542
        corrSecondN02701MinusPointP003Center2575)
    (embedPair2542 corrSecondN02701MinusPointP003Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP003DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP003Factor2575,
      corrSecondN02701MinusPointP003Error2575, rounding2542,
      corrSecondN02701MinusPointP003Radius2575]

theorem corrSecondN02701MinusPointP003DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP003Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP003RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP003Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP003Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP003Rounded2575]

def corrSecondN02701MinusPointP004Rounded2575 : RatPair2542 :=
  (((63726098544575275 : ℚ) /
        633825300114114700748351602688),
    (((-96574797251820649) : ℚ) /
        1267650600228229401496703205376))

noncomputable def corrSecondN02701MinusPointP004Radius2575 : ℝ := ((343666169645335 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701MinusPointP004RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP004Factor2575
        corrSecondN02701MinusPointP004Center2575) =
        corrSecondN02701MinusPointP004Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP004RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP004Rounded2575‖ ≤
          corrSecondN02701MinusPointP004Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP004Factor2575
      corrSecondN02701MinusPointP004Center2575)
  rw [corrSecondN02701MinusPointP004RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP004Factor2575 * embedPair2542
        corrSecondN02701MinusPointP004Center2575)
    (embedPair2542 corrSecondN02701MinusPointP004Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP004DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP004Factor2575,
      corrSecondN02701MinusPointP004Error2575, rounding2542,
      corrSecondN02701MinusPointP004Radius2575]

theorem corrSecondN02701MinusPointP004DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP004Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP004RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP004Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP004Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP004Rounded2575]

def corrSecondN02701MinusPointP005Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP005Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02701MinusPointP005RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP005Factor2575
        corrSecondN02701MinusPointP005Center2575) =
        corrSecondN02701MinusPointP005Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP005RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP005Rounded2575‖ ≤
          corrSecondN02701MinusPointP005Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP005Factor2575
      corrSecondN02701MinusPointP005Center2575)
  rw [corrSecondN02701MinusPointP005RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP005Factor2575 * embedPair2542
        corrSecondN02701MinusPointP005Center2575)
    (embedPair2542 corrSecondN02701MinusPointP005Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP005DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP005Factor2575,
      corrSecondN02701MinusPointP005Error2575, rounding2542,
      corrSecondN02701MinusPointP005Radius2575]

theorem corrSecondN02701MinusPointP005DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP005Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP005RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP005Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP005Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP005Rounded2575]

def corrSecondN02701MinusPointP006Rounded2575 : RatPair2542 :=
  (((23 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP006Radius2575 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701MinusPointP006RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP006Factor2575
        corrSecondN02701MinusPointP006Center2575) =
        corrSecondN02701MinusPointP006Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP006RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP006Rounded2575‖ ≤
          corrSecondN02701MinusPointP006Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP006Factor2575
      corrSecondN02701MinusPointP006Center2575)
  rw [corrSecondN02701MinusPointP006RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP006Factor2575 * embedPair2542
        corrSecondN02701MinusPointP006Center2575)
    (embedPair2542 corrSecondN02701MinusPointP006Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP006DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP006Factor2575,
      corrSecondN02701MinusPointP006Error2575, rounding2542,
      corrSecondN02701MinusPointP006Radius2575]

theorem corrSecondN02701MinusPointP006DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP006Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP006RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP006Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP006Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP006Rounded2575]

def corrSecondN02701MinusPointP007Rounded2575 : RatPair2542 :=
  (((35569883721463 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP007Radius2575 : ℝ := ((2203946193261 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701MinusPointP007RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP007Factor2575
        corrSecondN02701MinusPointP007Center2575) =
        corrSecondN02701MinusPointP007Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP007RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP007Rounded2575‖ ≤
          corrSecondN02701MinusPointP007Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP007Factor2575
      corrSecondN02701MinusPointP007Center2575)
  rw [corrSecondN02701MinusPointP007RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP007Factor2575 * embedPair2542
        corrSecondN02701MinusPointP007Center2575)
    (embedPair2542 corrSecondN02701MinusPointP007Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP007DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP007Factor2575,
      corrSecondN02701MinusPointP007Error2575, rounding2542,
      corrSecondN02701MinusPointP007Radius2575]

theorem corrSecondN02701MinusPointP007DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP007Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP007RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP007Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP007Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP007Rounded2575]

def corrSecondN02701MinusPointP008Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP008Radius2575 : ℝ := ((1100278695965 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701MinusPointP008RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP008Factor2575
        corrSecondN02701MinusPointP008Center2575) =
        corrSecondN02701MinusPointP008Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP008RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP008Rounded2575‖ ≤
          corrSecondN02701MinusPointP008Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP008Factor2575
      corrSecondN02701MinusPointP008Center2575)
  rw [corrSecondN02701MinusPointP008RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP008Factor2575 * embedPair2542
        corrSecondN02701MinusPointP008Center2575)
    (embedPair2542 corrSecondN02701MinusPointP008Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP008DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP008Factor2575,
      corrSecondN02701MinusPointP008Error2575, rounding2542,
      corrSecondN02701MinusPointP008Radius2575]

theorem corrSecondN02701MinusPointP008DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP008Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP008RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP008Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP008Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP008Rounded2575]

def corrSecondN02701MinusPointP009Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP009Radius2575 : ℝ := ((2200557392675 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701MinusPointP009RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP009Factor2575
        corrSecondN02701MinusPointP009Center2575) =
        corrSecondN02701MinusPointP009Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP009RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP009Rounded2575‖ ≤
          corrSecondN02701MinusPointP009Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP009Factor2575
      corrSecondN02701MinusPointP009Center2575)
  rw [corrSecondN02701MinusPointP009RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP009Factor2575 * embedPair2542
        corrSecondN02701MinusPointP009Center2575)
    (embedPair2542 corrSecondN02701MinusPointP009Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP009DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP009Factor2575,
      corrSecondN02701MinusPointP009Error2575, rounding2542,
      corrSecondN02701MinusPointP009Radius2575]

theorem corrSecondN02701MinusPointP009DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP009Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP009RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP009Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP009Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP009Rounded2575]

def corrSecondN02701MinusPointP010Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP010Radius2575 : ℝ := ((1100278696553 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701MinusPointP010RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP010Factor2575
        corrSecondN02701MinusPointP010Center2575) =
        corrSecondN02701MinusPointP010Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP010RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP010Rounded2575‖ ≤
          corrSecondN02701MinusPointP010Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP010Factor2575
      corrSecondN02701MinusPointP010Center2575)
  rw [corrSecondN02701MinusPointP010RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP010Factor2575 * embedPair2542
        corrSecondN02701MinusPointP010Center2575)
    (embedPair2542 corrSecondN02701MinusPointP010Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP010DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP010Factor2575,
      corrSecondN02701MinusPointP010Error2575, rounding2542,
      corrSecondN02701MinusPointP010Radius2575]

theorem corrSecondN02701MinusPointP010DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP010Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP010RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP010Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP010Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP010Rounded2575]

def corrSecondN02701MinusPointP011Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP011Radius2575 : ℝ := ((1100278696697 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701MinusPointP011RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP011Factor2575
        corrSecondN02701MinusPointP011Center2575) =
        corrSecondN02701MinusPointP011Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP011RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP011Rounded2575‖ ≤
          corrSecondN02701MinusPointP011Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP011Factor2575
      corrSecondN02701MinusPointP011Center2575)
  rw [corrSecondN02701MinusPointP011RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP011Factor2575 * embedPair2542
        corrSecondN02701MinusPointP011Center2575)
    (embedPair2542 corrSecondN02701MinusPointP011Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP011DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP011Factor2575,
      corrSecondN02701MinusPointP011Error2575, rounding2542,
      corrSecondN02701MinusPointP011Radius2575]

theorem corrSecondN02701MinusPointP011DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP011Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP011RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP011Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP011Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP011Rounded2575]

def corrSecondN02701MinusPointP012Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP012Radius2575 : ℝ := ((550139348423 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrSecondN02701MinusPointP012RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP012Factor2575
        corrSecondN02701MinusPointP012Center2575) =
        corrSecondN02701MinusPointP012Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP012RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP012Rounded2575‖ ≤
          corrSecondN02701MinusPointP012Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP012Factor2575
      corrSecondN02701MinusPointP012Center2575)
  rw [corrSecondN02701MinusPointP012RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP012Factor2575 * embedPair2542
        corrSecondN02701MinusPointP012Center2575)
    (embedPair2542 corrSecondN02701MinusPointP012Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP012DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP012Factor2575,
      corrSecondN02701MinusPointP012Error2575, rounding2542,
      corrSecondN02701MinusPointP012Radius2575]

theorem corrSecondN02701MinusPointP012DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP012Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP012RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP012Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP012Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP012Rounded2575]

def corrSecondN02701MinusPointP013Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP013Radius2575 : ℝ := ((550139348491 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrSecondN02701MinusPointP013RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP013Factor2575
        corrSecondN02701MinusPointP013Center2575) =
        corrSecondN02701MinusPointP013Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP013RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP013Rounded2575‖ ≤
          corrSecondN02701MinusPointP013Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP013Factor2575
      corrSecondN02701MinusPointP013Center2575)
  rw [corrSecondN02701MinusPointP013RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP013Factor2575 * embedPair2542
        corrSecondN02701MinusPointP013Center2575)
    (embedPair2542 corrSecondN02701MinusPointP013Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP013DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP013Factor2575,
      corrSecondN02701MinusPointP013Error2575, rounding2542,
      corrSecondN02701MinusPointP013Radius2575]

theorem corrSecondN02701MinusPointP013DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP013Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP013RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP013Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP013Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP013Rounded2575]

def corrSecondN02701MinusPointP014Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP014Radius2575 : ℝ := ((2200557394467 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701MinusPointP014RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP014Factor2575
        corrSecondN02701MinusPointP014Center2575) =
        corrSecondN02701MinusPointP014Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP014RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP014Rounded2575‖ ≤
          corrSecondN02701MinusPointP014Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP014Factor2575
      corrSecondN02701MinusPointP014Center2575)
  rw [corrSecondN02701MinusPointP014RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP014Factor2575 * embedPair2542
        corrSecondN02701MinusPointP014Center2575)
    (embedPair2542 corrSecondN02701MinusPointP014Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP014DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP014Factor2575,
      corrSecondN02701MinusPointP014Error2575, rounding2542,
      corrSecondN02701MinusPointP014Radius2575]

theorem corrSecondN02701MinusPointP014DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP014Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP014RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP014Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP014Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP014Rounded2575]

def corrSecondN02701MinusPointP015Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP015Radius2575 : ℝ := ((550139348707 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrSecondN02701MinusPointP015RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP015Factor2575
        corrSecondN02701MinusPointP015Center2575) =
        corrSecondN02701MinusPointP015Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP015RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP015Rounded2575‖ ≤
          corrSecondN02701MinusPointP015Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP015Factor2575
      corrSecondN02701MinusPointP015Center2575)
  rw [corrSecondN02701MinusPointP015RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP015Factor2575 * embedPair2542
        corrSecondN02701MinusPointP015Center2575)
    (embedPair2542 corrSecondN02701MinusPointP015Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP015DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP015Factor2575,
      corrSecondN02701MinusPointP015Error2575, rounding2542,
      corrSecondN02701MinusPointP015Radius2575]

theorem corrSecondN02701MinusPointP015DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP015Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP015RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP015Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP015Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP015Rounded2575]

def corrSecondN02701MinusPointP016Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP016Radius2575 : ℝ := ((137534837193 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem corrSecondN02701MinusPointP016RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP016Factor2575
        corrSecondN02701MinusPointP016Center2575) =
        corrSecondN02701MinusPointP016Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP016RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP016Rounded2575‖ ≤
          corrSecondN02701MinusPointP016Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP016Factor2575
      corrSecondN02701MinusPointP016Center2575)
  rw [corrSecondN02701MinusPointP016RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP016Factor2575 * embedPair2542
        corrSecondN02701MinusPointP016Center2575)
    (embedPair2542 corrSecondN02701MinusPointP016Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP016DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP016Factor2575,
      corrSecondN02701MinusPointP016Error2575, rounding2542,
      corrSecondN02701MinusPointP016Radius2575]

theorem corrSecondN02701MinusPointP016DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP016Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP016RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP016Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP016Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP016Rounded2575]

def corrSecondN02701MinusPointP017Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP017Radius2575 : ℝ := ((1100278697797 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701MinusPointP017RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP017Factor2575
        corrSecondN02701MinusPointP017Center2575) =
        corrSecondN02701MinusPointP017Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP017RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP017Rounded2575‖ ≤
          corrSecondN02701MinusPointP017Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP017Factor2575
      corrSecondN02701MinusPointP017Center2575)
  rw [corrSecondN02701MinusPointP017RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP017Factor2575 * embedPair2542
        corrSecondN02701MinusPointP017Center2575)
    (embedPair2542 corrSecondN02701MinusPointP017Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP017DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP017Factor2575,
      corrSecondN02701MinusPointP017Error2575, rounding2542,
      corrSecondN02701MinusPointP017Radius2575]

theorem corrSecondN02701MinusPointP017DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP017Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP017RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP017Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP017Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP017Rounded2575]

def corrSecondN02701MinusPointP018Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP018Radius2575 : ℝ := ((1100278697893 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701MinusPointP018RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP018Factor2575
        corrSecondN02701MinusPointP018Center2575) =
        corrSecondN02701MinusPointP018Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP018RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP018Rounded2575‖ ≤
          corrSecondN02701MinusPointP018Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP018Factor2575
      corrSecondN02701MinusPointP018Center2575)
  rw [corrSecondN02701MinusPointP018RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP018Factor2575 * embedPair2542
        corrSecondN02701MinusPointP018Center2575)
    (embedPair2542 corrSecondN02701MinusPointP018Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP018DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP018Factor2575,
      corrSecondN02701MinusPointP018Error2575, rounding2542,
      corrSecondN02701MinusPointP018Radius2575]

theorem corrSecondN02701MinusPointP018DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP018Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP018RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP018Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP018Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP018Rounded2575]

def corrSecondN02701MinusPointP019Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP019Radius2575 : ℝ := ((2200557396131 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701MinusPointP019RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP019Factor2575
        corrSecondN02701MinusPointP019Center2575) =
        corrSecondN02701MinusPointP019Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP019RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP019Rounded2575‖ ≤
          corrSecondN02701MinusPointP019Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP019Factor2575
      corrSecondN02701MinusPointP019Center2575)
  rw [corrSecondN02701MinusPointP019RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP019Factor2575 * embedPair2542
        corrSecondN02701MinusPointP019Center2575)
    (embedPair2542 corrSecondN02701MinusPointP019Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP019DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP019Factor2575,
      corrSecondN02701MinusPointP019Error2575, rounding2542,
      corrSecondN02701MinusPointP019Radius2575]

theorem corrSecondN02701MinusPointP019DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP019Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP019RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP019Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP019Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP019Rounded2575]

def corrSecondN02701MinusPointP020Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP020Radius2575 : ℝ := ((2200557396507 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701MinusPointP020RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP020Factor2575
        corrSecondN02701MinusPointP020Center2575) =
        corrSecondN02701MinusPointP020Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP020RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP020Rounded2575‖ ≤
          corrSecondN02701MinusPointP020Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP020Factor2575
      corrSecondN02701MinusPointP020Center2575)
  rw [corrSecondN02701MinusPointP020RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP020Factor2575 * embedPair2542
        corrSecondN02701MinusPointP020Center2575)
    (embedPair2542 corrSecondN02701MinusPointP020Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP020DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP020Factor2575,
      corrSecondN02701MinusPointP020Error2575, rounding2542,
      corrSecondN02701MinusPointP020Radius2575]

theorem corrSecondN02701MinusPointP020DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP020Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP020RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP020Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP020Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP020Rounded2575]

def corrSecondN02701MinusPointP021Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP021Radius2575 : ℝ := ((2200557396821 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701MinusPointP021RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP021Factor2575
        corrSecondN02701MinusPointP021Center2575) =
        corrSecondN02701MinusPointP021Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP021RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP021Rounded2575‖ ≤
          corrSecondN02701MinusPointP021Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP021Factor2575
      corrSecondN02701MinusPointP021Center2575)
  rw [corrSecondN02701MinusPointP021RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP021Factor2575 * embedPair2542
        corrSecondN02701MinusPointP021Center2575)
    (embedPair2542 corrSecondN02701MinusPointP021Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP021DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP021Factor2575,
      corrSecondN02701MinusPointP021Error2575, rounding2542,
      corrSecondN02701MinusPointP021Radius2575]

theorem corrSecondN02701MinusPointP021DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP021Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP021RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP021Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP021Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP021Rounded2575]

def corrSecondN02701MinusPointP022Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP022Radius2575 : ℝ := ((1100278698491 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701MinusPointP022RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP022Factor2575
        corrSecondN02701MinusPointP022Center2575) =
        corrSecondN02701MinusPointP022Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP022RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP022Rounded2575‖ ≤
          corrSecondN02701MinusPointP022Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP022Factor2575
      corrSecondN02701MinusPointP022Center2575)
  rw [corrSecondN02701MinusPointP022RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP022Factor2575 * embedPair2542
        corrSecondN02701MinusPointP022Center2575)
    (embedPair2542 corrSecondN02701MinusPointP022Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP022DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP022Factor2575,
      corrSecondN02701MinusPointP022Error2575, rounding2542,
      corrSecondN02701MinusPointP022Radius2575]

theorem corrSecondN02701MinusPointP022DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP022Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP022RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP022Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP022Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP022Rounded2575]

def corrSecondN02701MinusPointP023Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP023Radius2575 : ℝ := ((2200557397445 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701MinusPointP023RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP023Factor2575
        corrSecondN02701MinusPointP023Center2575) =
        corrSecondN02701MinusPointP023Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP023RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP023Rounded2575‖ ≤
          corrSecondN02701MinusPointP023Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP023Factor2575
      corrSecondN02701MinusPointP023Center2575)
  rw [corrSecondN02701MinusPointP023RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP023Factor2575 * embedPair2542
        corrSecondN02701MinusPointP023Center2575)
    (embedPair2542 corrSecondN02701MinusPointP023Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP023DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP023Factor2575,
      corrSecondN02701MinusPointP023Error2575, rounding2542,
      corrSecondN02701MinusPointP023Radius2575]

theorem corrSecondN02701MinusPointP023DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP023Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP023RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP023Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP023Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP023Rounded2575]

def corrSecondN02701MinusPointP024Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP024Radius2575 : ℝ := ((1100278698829 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701MinusPointP024RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP024Factor2575
        corrSecondN02701MinusPointP024Center2575) =
        corrSecondN02701MinusPointP024Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP024RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP024Rounded2575‖ ≤
          corrSecondN02701MinusPointP024Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP024Factor2575
      corrSecondN02701MinusPointP024Center2575)
  rw [corrSecondN02701MinusPointP024RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP024Factor2575 * embedPair2542
        corrSecondN02701MinusPointP024Center2575)
    (embedPair2542 corrSecondN02701MinusPointP024Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP024DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP024Factor2575,
      corrSecondN02701MinusPointP024Error2575, rounding2542,
      corrSecondN02701MinusPointP024Radius2575]

theorem corrSecondN02701MinusPointP024DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP024Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP024RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP024Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP024Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP024Rounded2575]

def corrSecondN02701MinusPointP025Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP025Radius2575 : ℝ := ((2200557397925 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701MinusPointP025RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP025Factor2575
        corrSecondN02701MinusPointP025Center2575) =
        corrSecondN02701MinusPointP025Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP025RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP025Rounded2575‖ ≤
          corrSecondN02701MinusPointP025Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP025Factor2575
      corrSecondN02701MinusPointP025Center2575)
  rw [corrSecondN02701MinusPointP025RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP025Factor2575 * embedPair2542
        corrSecondN02701MinusPointP025Center2575)
    (embedPair2542 corrSecondN02701MinusPointP025Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP025DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP025Factor2575,
      corrSecondN02701MinusPointP025Error2575, rounding2542,
      corrSecondN02701MinusPointP025Radius2575]

theorem corrSecondN02701MinusPointP025DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP025Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP025RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP025Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP025Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP025Rounded2575]

def corrSecondN02701MinusPointP026Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP026Radius2575 : ℝ := ((2200557398197 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701MinusPointP026RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP026Factor2575
        corrSecondN02701MinusPointP026Center2575) =
        corrSecondN02701MinusPointP026Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP026RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP026Rounded2575‖ ≤
          corrSecondN02701MinusPointP026Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP026Factor2575
      corrSecondN02701MinusPointP026Center2575)
  rw [corrSecondN02701MinusPointP026RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP026Factor2575 * embedPair2542
        corrSecondN02701MinusPointP026Center2575)
    (embedPair2542 corrSecondN02701MinusPointP026Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP026DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP026Factor2575,
      corrSecondN02701MinusPointP026Error2575, rounding2542,
      corrSecondN02701MinusPointP026Radius2575]

theorem corrSecondN02701MinusPointP026DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP026Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP026RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP026Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP026Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP026Rounded2575]

def corrSecondN02701MinusPointP027Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP027Radius2575 : ℝ := ((2200557398591 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701MinusPointP027RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP027Factor2575
        corrSecondN02701MinusPointP027Center2575) =
        corrSecondN02701MinusPointP027Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP027RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP027Rounded2575‖ ≤
          corrSecondN02701MinusPointP027Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP027Factor2575
      corrSecondN02701MinusPointP027Center2575)
  rw [corrSecondN02701MinusPointP027RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP027Factor2575 * embedPair2542
        corrSecondN02701MinusPointP027Center2575)
    (embedPair2542 corrSecondN02701MinusPointP027Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP027DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP027Factor2575,
      corrSecondN02701MinusPointP027Error2575, rounding2542,
      corrSecondN02701MinusPointP027Radius2575]

theorem corrSecondN02701MinusPointP027DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP027Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP027RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP027Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP027Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP027Rounded2575]

def corrSecondN02701MinusPointP028Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP028Radius2575 : ℝ := ((2200557398747 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701MinusPointP028RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP028Factor2575
        corrSecondN02701MinusPointP028Center2575) =
        corrSecondN02701MinusPointP028Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP028RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP028Rounded2575‖ ≤
          corrSecondN02701MinusPointP028Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP028Factor2575
      corrSecondN02701MinusPointP028Center2575)
  rw [corrSecondN02701MinusPointP028RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP028Factor2575 * embedPair2542
        corrSecondN02701MinusPointP028Center2575)
    (embedPair2542 corrSecondN02701MinusPointP028Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP028DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP028Factor2575,
      corrSecondN02701MinusPointP028Error2575, rounding2542,
      corrSecondN02701MinusPointP028Radius2575]

theorem corrSecondN02701MinusPointP028DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP028Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP028RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP028Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP028Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP028Rounded2575]

def corrSecondN02701MinusPointP029Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701MinusPointP029Radius2575 : ℝ := ((275069674873 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem corrSecondN02701MinusPointP029RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701MinusPointP029Factor2575
        corrSecondN02701MinusPointP029Center2575) =
        corrSecondN02701MinusPointP029Rounded2575 := by
  cbv

theorem corrSecondN02701MinusPointP029RoundedError2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02701MinusPointPosition2575 -
      embedPair2542 corrSecondN02701MinusPointP029Rounded2575‖ ≤
          corrSecondN02701MinusPointP029Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701MinusPointP029Factor2575
      corrSecondN02701MinusPointP029Center2575)
  rw [corrSecondN02701MinusPointP029RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP029Factor2575 * embedPair2542
        corrSecondN02701MinusPointP029Center2575)
    (embedPair2542 corrSecondN02701MinusPointP029Rounded2575)).trans (add_le_add
        corrSecondN02701MinusPointP029DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701MinusPointP029Factor2575,
      corrSecondN02701MinusPointP029Error2575, rounding2542,
      corrSecondN02701MinusPointP029Radius2575]

theorem corrSecondN02701MinusPointP029DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02701MinusPointPosition2575‖ ≤ 1 :=
        by
  have h := corrSecondN02701MinusPoint_triangle2575
    (weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02701MinusPointPosition2575)
    (embedPair2542 corrSecondN02701MinusPointP029Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701MinusPointP029RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701MinusPointP029Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701MinusPointP029Radius2575, pairMagnitude2542,
      corrSecondN02701MinusPointP029Rounded2575]

noncomputable def corrSecondN02701MinusSignedValue2575 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 corrSecondN02701MinusPointP000Rounded2575
  | 1 => embedPair2542 corrSecondN02701MinusPointP001Rounded2575
  | 2 => embedPair2542 corrSecondN02701MinusPointP002Rounded2575
  | 3 => embedPair2542 corrSecondN02701MinusPointP003Rounded2575
  | 4 => embedPair2542 corrSecondN02701MinusPointP004Rounded2575
  | 5 => embedPair2542 corrSecondN02701MinusPointP005Rounded2575
  | 6 => embedPair2542 corrSecondN02701MinusPointP006Rounded2575
  | 7 => embedPair2542 corrSecondN02701MinusPointP007Rounded2575
  | 8 => embedPair2542 corrSecondN02701MinusPointP008Rounded2575
  | 9 => embedPair2542 corrSecondN02701MinusPointP009Rounded2575
  | 10 => embedPair2542 corrSecondN02701MinusPointP010Rounded2575
  | 11 => embedPair2542 corrSecondN02701MinusPointP011Rounded2575
  | 12 => embedPair2542 corrSecondN02701MinusPointP012Rounded2575
  | 13 => embedPair2542 corrSecondN02701MinusPointP013Rounded2575
  | 14 => embedPair2542 corrSecondN02701MinusPointP014Rounded2575
  | 15 => embedPair2542 corrSecondN02701MinusPointP015Rounded2575
  | 16 => embedPair2542 corrSecondN02701MinusPointP016Rounded2575
  | 17 => embedPair2542 corrSecondN02701MinusPointP017Rounded2575
  | 18 => embedPair2542 corrSecondN02701MinusPointP018Rounded2575
  | 19 => embedPair2542 corrSecondN02701MinusPointP019Rounded2575
  | 20 => embedPair2542 corrSecondN02701MinusPointP020Rounded2575
  | 21 => embedPair2542 corrSecondN02701MinusPointP021Rounded2575
  | 22 => embedPair2542 corrSecondN02701MinusPointP022Rounded2575
  | 23 => embedPair2542 corrSecondN02701MinusPointP023Rounded2575
  | 24 => embedPair2542 corrSecondN02701MinusPointP024Rounded2575
  | 25 => embedPair2542 corrSecondN02701MinusPointP025Rounded2575
  | 26 => embedPair2542 corrSecondN02701MinusPointP026Rounded2575
  | 27 => embedPair2542 corrSecondN02701MinusPointP027Rounded2575
  | 28 => embedPair2542 corrSecondN02701MinusPointP028Rounded2575
  | 29 => embedPair2542 corrSecondN02701MinusPointP029Rounded2575
  | _ => 0

noncomputable def corrSecondN02701MinusSignedError2575 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => corrSecondN02701MinusPointP000Radius2575
  | 1 => corrSecondN02701MinusPointP001Radius2575
  | 2 => corrSecondN02701MinusPointP002Radius2575
  | 3 => corrSecondN02701MinusPointP003Radius2575
  | 4 => corrSecondN02701MinusPointP004Radius2575
  | 5 => corrSecondN02701MinusPointP005Radius2575
  | 6 => corrSecondN02701MinusPointP006Radius2575
  | 7 => corrSecondN02701MinusPointP007Radius2575
  | 8 => corrSecondN02701MinusPointP008Radius2575
  | 9 => corrSecondN02701MinusPointP009Radius2575
  | 10 => corrSecondN02701MinusPointP010Radius2575
  | 11 => corrSecondN02701MinusPointP011Radius2575
  | 12 => corrSecondN02701MinusPointP012Radius2575
  | 13 => corrSecondN02701MinusPointP013Radius2575
  | 14 => corrSecondN02701MinusPointP014Radius2575
  | 15 => corrSecondN02701MinusPointP015Radius2575
  | 16 => corrSecondN02701MinusPointP016Radius2575
  | 17 => corrSecondN02701MinusPointP017Radius2575
  | 18 => corrSecondN02701MinusPointP018Radius2575
  | 19 => corrSecondN02701MinusPointP019Radius2575
  | 20 => corrSecondN02701MinusPointP020Radius2575
  | 21 => corrSecondN02701MinusPointP021Radius2575
  | 22 => corrSecondN02701MinusPointP022Radius2575
  | 23 => corrSecondN02701MinusPointP023Radius2575
  | 24 => corrSecondN02701MinusPointP024Radius2575
  | 25 => corrSecondN02701MinusPointP025Radius2575
  | 26 => corrSecondN02701MinusPointP026Radius2575
  | 27 => corrSecondN02701MinusPointP027Radius2575
  | 28 => corrSecondN02701MinusPointP028Radius2575
  | 29 => corrSecondN02701MinusPointP029Radius2575
  | _ => 0

theorem corrSecondN02701MinusSignedExpError2575 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrSecondN02701MinusPointPosition2575 -
        corrSecondN02701MinusSignedValue2575 i‖ ≤ corrSecondN02701MinusSignedError2575 i := by
  fin_cases i
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP000RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP001RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP002RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP003RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP004RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP005RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP006RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP007RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP008RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP009RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP010RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP011RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP012RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP013RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP014RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP015RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP016RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP017RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP018RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP019RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP020RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP021RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP022RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP023RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP024RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP025RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP026RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP027RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP028RoundedError2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP029RoundedError2575

theorem corrSecondN02701MinusSignedUnitNorm2575 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrSecondN02701MinusPointPosition2575‖ ≤ 1
        := by
  fin_cases i
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP000DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP001DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP002DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP003DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP004DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP005DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP006DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP007DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP008DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP009DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP010DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP011DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP012DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP013DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP014DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP015DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP016DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP017DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP018DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP019DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP020DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP021DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP022DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP023DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP024DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP025DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP026DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP027DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP028DerivativeNorm2575
  · simpa only [corrSecondN02701MinusSignedValue2575, corrSecondN02701MinusSignedError2575] using
      corrSecondN02701MinusPointP029DerivativeNorm2575

noncomputable def corrSecondN02701MinusSignedSum2575 : ℂ := ⟨(((-(((8116033180039 * 10^40
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

noncomputable def corrSecondN02701MinusSignedUpper2575 : ℝ := ((1228688317 : ℝ) /
        50000000)

theorem corrSecondN02701MinusSignedSum_eq2575 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSecondN02701MinusSignedValue2575 i) =
      corrSecondN02701MinusSignedSum2575 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        corrSecondN02701MinusSignedValue2575,
      corrSecondN02701MinusSignedSum2575, embedPair2542,
          corrSecondN02701MinusPointP000Rounded2575,
      corrSecondN02701MinusPointP001Rounded2575,
      corrSecondN02701MinusPointP002Rounded2575,
      corrSecondN02701MinusPointP003Rounded2575,
      corrSecondN02701MinusPointP004Rounded2575,
      corrSecondN02701MinusPointP005Rounded2575,
      corrSecondN02701MinusPointP006Rounded2575,
      corrSecondN02701MinusPointP007Rounded2575,
      corrSecondN02701MinusPointP008Rounded2575,
      corrSecondN02701MinusPointP009Rounded2575,
      corrSecondN02701MinusPointP010Rounded2575,
      corrSecondN02701MinusPointP011Rounded2575,
      corrSecondN02701MinusPointP012Rounded2575,
      corrSecondN02701MinusPointP013Rounded2575,
      corrSecondN02701MinusPointP014Rounded2575,
      corrSecondN02701MinusPointP015Rounded2575,
      corrSecondN02701MinusPointP016Rounded2575,
      corrSecondN02701MinusPointP017Rounded2575,
      corrSecondN02701MinusPointP018Rounded2575,
      corrSecondN02701MinusPointP019Rounded2575,
      corrSecondN02701MinusPointP020Rounded2575,
      corrSecondN02701MinusPointP021Rounded2575,
      corrSecondN02701MinusPointP022Rounded2575,
      corrSecondN02701MinusPointP023Rounded2575,
      corrSecondN02701MinusPointP024Rounded2575,
      corrSecondN02701MinusPointP025Rounded2575,
      corrSecondN02701MinusPointP026Rounded2575,
      corrSecondN02701MinusPointP027Rounded2575,
      corrSecondN02701MinusPointP028Rounded2575,
      corrSecondN02701MinusPointP029Rounded2575, Complex.mul_re, Complex.mul_im]

theorem corrSecondN02701MinusSignedSum_norm2575 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSecondN02701MinusSignedValue2575 i‖ ≤
        ((153586039 :
        ℝ) /
        6250000) := by
  rw [corrSecondN02701MinusSignedSum_eq2575]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [corrSecondN02701MinusSignedSum2575]

theorem corrSecondN02701MinusSignedCharge2575 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * corrSecondN02701MinusSignedError2575 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      corrSecondN02701MinusSignedError2575, corrSecondN02701MinusPointP000Radius2575,
      corrSecondN02701MinusPointP001Radius2575,
      corrSecondN02701MinusPointP002Radius2575,
      corrSecondN02701MinusPointP003Radius2575,
      corrSecondN02701MinusPointP004Radius2575,
      corrSecondN02701MinusPointP005Radius2575,
      corrSecondN02701MinusPointP006Radius2575,
      corrSecondN02701MinusPointP007Radius2575,
      corrSecondN02701MinusPointP008Radius2575,
      corrSecondN02701MinusPointP009Radius2575,
      corrSecondN02701MinusPointP010Radius2575,
      corrSecondN02701MinusPointP011Radius2575,
      corrSecondN02701MinusPointP012Radius2575,
      corrSecondN02701MinusPointP013Radius2575,
      corrSecondN02701MinusPointP014Radius2575,
      corrSecondN02701MinusPointP015Radius2575,
      corrSecondN02701MinusPointP016Radius2575,
      corrSecondN02701MinusPointP017Radius2575,
      corrSecondN02701MinusPointP018Radius2575,
      corrSecondN02701MinusPointP019Radius2575,
      corrSecondN02701MinusPointP020Radius2575,
      corrSecondN02701MinusPointP021Radius2575,
      corrSecondN02701MinusPointP022Radius2575,
      corrSecondN02701MinusPointP023Radius2575,
      corrSecondN02701MinusPointP024Radius2575,
      corrSecondN02701MinusPointP025Radius2575,
      corrSecondN02701MinusPointP026Radius2575,
      corrSecondN02701MinusPointP027Radius2575,
      corrSecondN02701MinusPointP028Radius2575,
      corrSecondN02701MinusPointP029Radius2575]

theorem corrSecondN02701MinusSignedUpper_le2575 :
    signedJetUpper2539 2 (-1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 corrSecondN02701MinusPointPosition2575 ≤
          corrSecondN02701MinusSignedUpper2575 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrSecondN02701MinusPointPosition2575‖
            ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSecondN02701MinusSignedValue2575 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * corrSecondN02701MinusSignedError2575 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (corrSecondN02701MinusSignedExpError2575 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrSecondN02701MinusPointPosition2575‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (corrSecondN02701MinusSignedUnitNorm2575 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 i corrSecondN02701MinusPointPosition2575‖)
          ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 corrSecondN02701MinusSignedUpper2575
  linarith [corrSecondN02701MinusSignedSum_norm2575, corrSecondN02701MinusSignedCharge2575]

theorem corrSecondN02701MinusPhysical2575 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        corrSecondN02701MinusPointPosition2575‖ ≤
      corrSecondN02701MinusSignedUpper2575 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        corrSecondN02701MinusPointPosition2575
  exact h.trans corrSecondN02701MinusSignedUpper_le2575

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusSignedExpError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusSignedSum_eq2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusSignedCharge2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusSignedUpper_le2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701MinusPhysical2575
