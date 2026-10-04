import ConnesWeilRH.Dev.C1RouteACorrSecondN02701PlusDerivatives2575
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem corrSecondN02701PlusPoint_triangle2575 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def corrSecondN02701PlusPointP000Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP000Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02701PlusPointP000RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP000Factor2575
        corrSecondN02701PlusPointP000Center2575) =
        corrSecondN02701PlusPointP000Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP000RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP000Rounded2575‖ ≤
          corrSecondN02701PlusPointP000Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP000Factor2575
      corrSecondN02701PlusPointP000Center2575)
  rw [corrSecondN02701PlusPointP000RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP000Factor2575 * embedPair2542
        corrSecondN02701PlusPointP000Center2575)
    (embedPair2542 corrSecondN02701PlusPointP000Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP000DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP000Factor2575,
      corrSecondN02701PlusPointP000Error2575, rounding2542,
      corrSecondN02701PlusPointP000Radius2575]

theorem corrSecondN02701PlusPointP000DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP000Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP000RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP000Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP000Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP000Rounded2575]

def corrSecondN02701PlusPointP001Rounded2575 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP001Radius2575 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701PlusPointP001RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP001Factor2575
        corrSecondN02701PlusPointP001Center2575) =
        corrSecondN02701PlusPointP001Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP001RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP001Rounded2575‖ ≤
          corrSecondN02701PlusPointP001Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP001Factor2575
      corrSecondN02701PlusPointP001Center2575)
  rw [corrSecondN02701PlusPointP001RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP001Factor2575 * embedPair2542
        corrSecondN02701PlusPointP001Center2575)
    (embedPair2542 corrSecondN02701PlusPointP001Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP001DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP001Factor2575,
      corrSecondN02701PlusPointP001Error2575, rounding2542,
      corrSecondN02701PlusPointP001Radius2575]

theorem corrSecondN02701PlusPointP001DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP001Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP001RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP001Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP001Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP001Rounded2575]

def corrSecondN02701PlusPointP002Rounded2575 : RatPair2542 :=
  (((1402803 : ℚ) /
        1267650600228229401496703205376),
    (((-1040939) : ℚ) /
        1267650600228229401496703205376))

noncomputable def corrSecondN02701PlusPointP002Radius2575 : ℝ := ((137438953899 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem corrSecondN02701PlusPointP002RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP002Factor2575
        corrSecondN02701PlusPointP002Center2575) =
        corrSecondN02701PlusPointP002Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP002RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP002Rounded2575‖ ≤
          corrSecondN02701PlusPointP002Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP002Factor2575
      corrSecondN02701PlusPointP002Center2575)
  rw [corrSecondN02701PlusPointP002RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP002Factor2575 * embedPair2542
        corrSecondN02701PlusPointP002Center2575)
    (embedPair2542 corrSecondN02701PlusPointP002Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP002DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP002Factor2575,
      corrSecondN02701PlusPointP002Error2575, rounding2542,
      corrSecondN02701PlusPointP002Radius2575]

theorem corrSecondN02701PlusPointP002DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP002Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP002RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP002Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP002Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP002Rounded2575]

def corrSecondN02701PlusPointP003Rounded2575 : RatPair2542 :=
  (((7745090122567 : ℚ) /
        633825300114114700748351602688),
    ((529330151187 : ℚ) /
        158456325028528675187087900672))

noncomputable def corrSecondN02701PlusPointP003Radius2575 : ℝ := ((569518697377 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrSecondN02701PlusPointP003RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP003Factor2575
        corrSecondN02701PlusPointP003Center2575) =
        corrSecondN02701PlusPointP003Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP003RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP003Rounded2575‖ ≤
          corrSecondN02701PlusPointP003Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP003Factor2575
      corrSecondN02701PlusPointP003Center2575)
  rw [corrSecondN02701PlusPointP003RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP003Factor2575 * embedPair2542
        corrSecondN02701PlusPointP003Center2575)
    (embedPair2542 corrSecondN02701PlusPointP003Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP003DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP003Factor2575,
      corrSecondN02701PlusPointP003Error2575, rounding2542,
      corrSecondN02701PlusPointP003Radius2575]

theorem corrSecondN02701PlusPointP003DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP003Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP003RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP003Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP003Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP003Rounded2575]

def corrSecondN02701PlusPointP004Rounded2575 : RatPair2542 :=
  (((6023965667843215 : ℚ) /
        1267650600228229401496703205376),
    (((-4114681970563725) : ℚ) /
        1267650600228229401496703205376))

noncomputable def corrSecondN02701PlusPointP004Radius2575 : ℝ := ((34548168877549 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701PlusPointP004RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP004Factor2575
        corrSecondN02701PlusPointP004Center2575) =
        corrSecondN02701PlusPointP004Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP004RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP004Rounded2575‖ ≤
          corrSecondN02701PlusPointP004Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP004Factor2575
      corrSecondN02701PlusPointP004Center2575)
  rw [corrSecondN02701PlusPointP004RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP004Factor2575 * embedPair2542
        corrSecondN02701PlusPointP004Center2575)
    (embedPair2542 corrSecondN02701PlusPointP004Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP004DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP004Factor2575,
      corrSecondN02701PlusPointP004Error2575, rounding2542,
      corrSecondN02701PlusPointP004Radius2575]

theorem corrSecondN02701PlusPointP004DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP004Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP004RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP004Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP004Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP004Rounded2575]

def corrSecondN02701PlusPointP005Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP005Radius2575 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem corrSecondN02701PlusPointP005RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP005Factor2575
        corrSecondN02701PlusPointP005Center2575) =
        corrSecondN02701PlusPointP005Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP005RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP005Rounded2575‖ ≤
          corrSecondN02701PlusPointP005Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP005Factor2575
      corrSecondN02701PlusPointP005Center2575)
  rw [corrSecondN02701PlusPointP005RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP005Factor2575 * embedPair2542
        corrSecondN02701PlusPointP005Center2575)
    (embedPair2542 corrSecondN02701PlusPointP005Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP005DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP005Factor2575,
      corrSecondN02701PlusPointP005Error2575, rounding2542,
      corrSecondN02701PlusPointP005Radius2575]

theorem corrSecondN02701PlusPointP005DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP005Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP005RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP005Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP005Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP005Rounded2575]

def corrSecondN02701PlusPointP006Rounded2575 : RatPair2542 :=
  (((1 : ℚ) /
        316912650057057350374175801344),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP006Radius2575 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701PlusPointP006RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP006Factor2575
        corrSecondN02701PlusPointP006Center2575) =
        corrSecondN02701PlusPointP006Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP006RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP006Rounded2575‖ ≤
          corrSecondN02701PlusPointP006Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP006Factor2575
      corrSecondN02701PlusPointP006Center2575)
  rw [corrSecondN02701PlusPointP006RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP006Factor2575 * embedPair2542
        corrSecondN02701PlusPointP006Center2575)
    (embedPair2542 corrSecondN02701PlusPointP006Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP006DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP006Factor2575,
      corrSecondN02701PlusPointP006Error2575, rounding2542,
      corrSecondN02701PlusPointP006Radius2575]

theorem corrSecondN02701PlusPointP006DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP006Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP006RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP006Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP006Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP006Rounded2575]

def corrSecondN02701PlusPointP007Rounded2575 : RatPair2542 :=
  (((1868106838301 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP007Radius2575 : ℝ := ((549823655285 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrSecondN02701PlusPointP007RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP007Factor2575
        corrSecondN02701PlusPointP007Center2575) =
        corrSecondN02701PlusPointP007Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP007RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP007Rounded2575‖ ≤
          corrSecondN02701PlusPointP007Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP007Factor2575
      corrSecondN02701PlusPointP007Center2575)
  rw [corrSecondN02701PlusPointP007RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP007Factor2575 * embedPair2542
        corrSecondN02701PlusPointP007Center2575)
    (embedPair2542 corrSecondN02701PlusPointP007Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP007DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP007Factor2575,
      corrSecondN02701PlusPointP007Error2575, rounding2542,
      corrSecondN02701PlusPointP007Radius2575]

theorem corrSecondN02701PlusPointP007DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP007Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP007RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP007Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP007Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP007Rounded2575]

def corrSecondN02701PlusPointP008Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP008Radius2575 : ℝ := ((1100278696019 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701PlusPointP008RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP008Factor2575
        corrSecondN02701PlusPointP008Center2575) =
        corrSecondN02701PlusPointP008Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP008RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP008Rounded2575‖ ≤
          corrSecondN02701PlusPointP008Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP008Factor2575
      corrSecondN02701PlusPointP008Center2575)
  rw [corrSecondN02701PlusPointP008RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP008Factor2575 * embedPair2542
        corrSecondN02701PlusPointP008Center2575)
    (embedPair2542 corrSecondN02701PlusPointP008Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP008DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP008Factor2575,
      corrSecondN02701PlusPointP008Error2575, rounding2542,
      corrSecondN02701PlusPointP008Radius2575]

theorem corrSecondN02701PlusPointP008DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP008Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP008RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP008Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP008Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP008Rounded2575]

def corrSecondN02701PlusPointP009Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP009Radius2575 : ℝ := ((2200557392783 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701PlusPointP009RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP009Factor2575
        corrSecondN02701PlusPointP009Center2575) =
        corrSecondN02701PlusPointP009Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP009RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP009Rounded2575‖ ≤
          corrSecondN02701PlusPointP009Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP009Factor2575
      corrSecondN02701PlusPointP009Center2575)
  rw [corrSecondN02701PlusPointP009RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP009Factor2575 * embedPair2542
        corrSecondN02701PlusPointP009Center2575)
    (embedPair2542 corrSecondN02701PlusPointP009Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP009DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP009Factor2575,
      corrSecondN02701PlusPointP009Error2575, rounding2542,
      corrSecondN02701PlusPointP009Radius2575]

theorem corrSecondN02701PlusPointP009DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP009Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP009RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP009Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP009Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP009Rounded2575]

def corrSecondN02701PlusPointP010Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP010Radius2575 : ℝ := ((2200557393215 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701PlusPointP010RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP010Factor2575
        corrSecondN02701PlusPointP010Center2575) =
        corrSecondN02701PlusPointP010Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP010RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP010Rounded2575‖ ≤
          corrSecondN02701PlusPointP010Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP010Factor2575
      corrSecondN02701PlusPointP010Center2575)
  rw [corrSecondN02701PlusPointP010RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP010Factor2575 * embedPair2542
        corrSecondN02701PlusPointP010Center2575)
    (embedPair2542 corrSecondN02701PlusPointP010Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP010DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP010Factor2575,
      corrSecondN02701PlusPointP010Error2575, rounding2542,
      corrSecondN02701PlusPointP010Radius2575]

theorem corrSecondN02701PlusPointP010DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP010Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP010RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP010Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP010Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP010Rounded2575]

def corrSecondN02701PlusPointP011Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP011Radius2575 : ℝ := ((1100278696751 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701PlusPointP011RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP011Factor2575
        corrSecondN02701PlusPointP011Center2575) =
        corrSecondN02701PlusPointP011Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP011RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP011Rounded2575‖ ≤
          corrSecondN02701PlusPointP011Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP011Factor2575
      corrSecondN02701PlusPointP011Center2575)
  rw [corrSecondN02701PlusPointP011RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP011Factor2575 * embedPair2542
        corrSecondN02701PlusPointP011Center2575)
    (embedPair2542 corrSecondN02701PlusPointP011Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP011DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP011Factor2575,
      corrSecondN02701PlusPointP011Error2575, rounding2542,
      corrSecondN02701PlusPointP011Radius2575]

theorem corrSecondN02701PlusPointP011DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP011Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP011RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP011Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP011Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP011Rounded2575]

def corrSecondN02701PlusPointP012Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP012Radius2575 : ℝ := ((275069674225 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem corrSecondN02701PlusPointP012RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP012Factor2575
        corrSecondN02701PlusPointP012Center2575) =
        corrSecondN02701PlusPointP012Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP012RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP012Rounded2575‖ ≤
          corrSecondN02701PlusPointP012Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP012Factor2575
      corrSecondN02701PlusPointP012Center2575)
  rw [corrSecondN02701PlusPointP012RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP012Factor2575 * embedPair2542
        corrSecondN02701PlusPointP012Center2575)
    (embedPair2542 corrSecondN02701PlusPointP012Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP012DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP012Factor2575,
      corrSecondN02701PlusPointP012Error2575, rounding2542,
      corrSecondN02701PlusPointP012Radius2575]

theorem corrSecondN02701PlusPointP012DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP012Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP012RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP012Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP012Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP012Rounded2575]

def corrSecondN02701PlusPointP013Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP013Radius2575 : ℝ := ((275069674259 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem corrSecondN02701PlusPointP013RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP013Factor2575
        corrSecondN02701PlusPointP013Center2575) =
        corrSecondN02701PlusPointP013Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP013RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP013Rounded2575‖ ≤
          corrSecondN02701PlusPointP013Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP013Factor2575
      corrSecondN02701PlusPointP013Center2575)
  rw [corrSecondN02701PlusPointP013RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP013Factor2575 * embedPair2542
        corrSecondN02701PlusPointP013Center2575)
    (embedPair2542 corrSecondN02701PlusPointP013Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP013DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP013Factor2575,
      corrSecondN02701PlusPointP013Error2575, rounding2542,
      corrSecondN02701PlusPointP013Radius2575]

theorem corrSecondN02701PlusPointP013DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP013Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP013RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP013Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP013Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP013Rounded2575]

def corrSecondN02701PlusPointP014Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP014Radius2575 : ℝ := ((2200557394575 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701PlusPointP014RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP014Factor2575
        corrSecondN02701PlusPointP014Center2575) =
        corrSecondN02701PlusPointP014Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP014RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP014Rounded2575‖ ≤
          corrSecondN02701PlusPointP014Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP014Factor2575
      corrSecondN02701PlusPointP014Center2575)
  rw [corrSecondN02701PlusPointP014RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP014Factor2575 * embedPair2542
        corrSecondN02701PlusPointP014Center2575)
    (embedPair2542 corrSecondN02701PlusPointP014Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP014DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP014Factor2575,
      corrSecondN02701PlusPointP014Error2575, rounding2542,
      corrSecondN02701PlusPointP014Radius2575]

theorem corrSecondN02701PlusPointP014DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP014Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP014RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP014Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP014Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP014Rounded2575]

def corrSecondN02701PlusPointP015Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP015Radius2575 : ℝ := ((275069674367 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem corrSecondN02701PlusPointP015RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP015Factor2575
        corrSecondN02701PlusPointP015Center2575) =
        corrSecondN02701PlusPointP015Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP015RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP015Rounded2575‖ ≤
          corrSecondN02701PlusPointP015Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP015Factor2575
      corrSecondN02701PlusPointP015Center2575)
  rw [corrSecondN02701PlusPointP015RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP015Factor2575 * embedPair2542
        corrSecondN02701PlusPointP015Center2575)
    (embedPair2542 corrSecondN02701PlusPointP015Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP015DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP015Factor2575,
      corrSecondN02701PlusPointP015Error2575, rounding2542,
      corrSecondN02701PlusPointP015Radius2575]

theorem corrSecondN02701PlusPointP015DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP015Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP015RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP015Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP015Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP015Rounded2575]

def corrSecondN02701PlusPointP016Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP016Radius2575 : ℝ := ((550139348799 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrSecondN02701PlusPointP016RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP016Factor2575
        corrSecondN02701PlusPointP016Center2575) =
        corrSecondN02701PlusPointP016Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP016RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP016Rounded2575‖ ≤
          corrSecondN02701PlusPointP016Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP016Factor2575
      corrSecondN02701PlusPointP016Center2575)
  rw [corrSecondN02701PlusPointP016RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP016Factor2575 * embedPair2542
        corrSecondN02701PlusPointP016Center2575)
    (embedPair2542 corrSecondN02701PlusPointP016Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP016DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP016Factor2575,
      corrSecondN02701PlusPointP016Error2575, rounding2542,
      corrSecondN02701PlusPointP016Radius2575]

theorem corrSecondN02701PlusPointP016DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP016Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP016RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP016Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP016Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP016Rounded2575]

def corrSecondN02701PlusPointP017Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP017Radius2575 : ℝ := ((1100278697851 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701PlusPointP017RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP017Factor2575
        corrSecondN02701PlusPointP017Center2575) =
        corrSecondN02701PlusPointP017Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP017RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP017Rounded2575‖ ≤
          corrSecondN02701PlusPointP017Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP017Factor2575
      corrSecondN02701PlusPointP017Center2575)
  rw [corrSecondN02701PlusPointP017RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP017Factor2575 * embedPair2542
        corrSecondN02701PlusPointP017Center2575)
    (embedPair2542 corrSecondN02701PlusPointP017Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP017DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP017Factor2575,
      corrSecondN02701PlusPointP017Error2575, rounding2542,
      corrSecondN02701PlusPointP017Radius2575]

theorem corrSecondN02701PlusPointP017DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP017Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP017RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP017Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP017Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP017Rounded2575]

def corrSecondN02701PlusPointP018Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP018Radius2575 : ℝ := ((1100278697947 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701PlusPointP018RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP018Factor2575
        corrSecondN02701PlusPointP018Center2575) =
        corrSecondN02701PlusPointP018Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP018RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP018Rounded2575‖ ≤
          corrSecondN02701PlusPointP018Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP018Factor2575
      corrSecondN02701PlusPointP018Center2575)
  rw [corrSecondN02701PlusPointP018RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP018Factor2575 * embedPair2542
        corrSecondN02701PlusPointP018Center2575)
    (embedPair2542 corrSecondN02701PlusPointP018Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP018DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP018Factor2575,
      corrSecondN02701PlusPointP018Error2575, rounding2542,
      corrSecondN02701PlusPointP018Radius2575]

theorem corrSecondN02701PlusPointP018DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP018Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP018RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP018Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP018Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP018Rounded2575]

def corrSecondN02701PlusPointP019Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP019Radius2575 : ℝ := ((137534837265 : ℝ) /
        (8 * 10^40
        + 7112285931760246646623899502532662132736))

theorem corrSecondN02701PlusPointP019RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP019Factor2575
        corrSecondN02701PlusPointP019Center2575) =
        corrSecondN02701PlusPointP019Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP019RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP019Rounded2575‖ ≤
          corrSecondN02701PlusPointP019Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP019Factor2575
      corrSecondN02701PlusPointP019Center2575)
  rw [corrSecondN02701PlusPointP019RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP019Factor2575 * embedPair2542
        corrSecondN02701PlusPointP019Center2575)
    (embedPair2542 corrSecondN02701PlusPointP019Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP019DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP019Factor2575,
      corrSecondN02701PlusPointP019Error2575, rounding2542,
      corrSecondN02701PlusPointP019Radius2575]

theorem corrSecondN02701PlusPointP019DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP019Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP019RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP019Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP019Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP019Rounded2575]

def corrSecondN02701PlusPointP020Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP020Radius2575 : ℝ := ((275069674577 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem corrSecondN02701PlusPointP020RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP020Factor2575
        corrSecondN02701PlusPointP020Center2575) =
        corrSecondN02701PlusPointP020Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP020RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP020Rounded2575‖ ≤
          corrSecondN02701PlusPointP020Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP020Factor2575
      corrSecondN02701PlusPointP020Center2575)
  rw [corrSecondN02701PlusPointP020RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP020Factor2575 * embedPair2542
        corrSecondN02701PlusPointP020Center2575)
    (embedPair2542 corrSecondN02701PlusPointP020Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP020DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP020Factor2575,
      corrSecondN02701PlusPointP020Error2575, rounding2542,
      corrSecondN02701PlusPointP020Radius2575]

theorem corrSecondN02701PlusPointP020DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP020Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP020RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP020Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP020Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP020Rounded2575]

def corrSecondN02701PlusPointP021Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP021Radius2575 : ℝ := ((2200557396929 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701PlusPointP021RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP021Factor2575
        corrSecondN02701PlusPointP021Center2575) =
        corrSecondN02701PlusPointP021Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP021RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP021Rounded2575‖ ≤
          corrSecondN02701PlusPointP021Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP021Factor2575
      corrSecondN02701PlusPointP021Center2575)
  rw [corrSecondN02701PlusPointP021RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP021Factor2575 * embedPair2542
        corrSecondN02701PlusPointP021Center2575)
    (embedPair2542 corrSecondN02701PlusPointP021Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP021DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP021Factor2575,
      corrSecondN02701PlusPointP021Error2575, rounding2542,
      corrSecondN02701PlusPointP021Radius2575]

theorem corrSecondN02701PlusPointP021DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP021Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP021RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP021Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP021Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP021Rounded2575]

def corrSecondN02701PlusPointP022Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP022Radius2575 : ℝ := ((1100278698545 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701PlusPointP022RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP022Factor2575
        corrSecondN02701PlusPointP022Center2575) =
        corrSecondN02701PlusPointP022Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP022RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP022Rounded2575‖ ≤
          corrSecondN02701PlusPointP022Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP022Factor2575
      corrSecondN02701PlusPointP022Center2575)
  rw [corrSecondN02701PlusPointP022RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP022Factor2575 * embedPair2542
        corrSecondN02701PlusPointP022Center2575)
    (embedPair2542 corrSecondN02701PlusPointP022Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP022DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP022Factor2575,
      corrSecondN02701PlusPointP022Error2575, rounding2542,
      corrSecondN02701PlusPointP022Radius2575]

theorem corrSecondN02701PlusPointP022DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP022Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP022RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP022Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP022Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP022Rounded2575]

def corrSecondN02701PlusPointP023Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP023Radius2575 : ℝ := ((2200557397553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701PlusPointP023RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP023Factor2575
        corrSecondN02701PlusPointP023Center2575) =
        corrSecondN02701PlusPointP023Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP023RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP023Rounded2575‖ ≤
          corrSecondN02701PlusPointP023Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP023Factor2575
      corrSecondN02701PlusPointP023Center2575)
  rw [corrSecondN02701PlusPointP023RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP023Factor2575 * embedPair2542
        corrSecondN02701PlusPointP023Center2575)
    (embedPair2542 corrSecondN02701PlusPointP023Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP023DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP023Factor2575,
      corrSecondN02701PlusPointP023Error2575, rounding2542,
      corrSecondN02701PlusPointP023Radius2575]

theorem corrSecondN02701PlusPointP023DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP023Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP023RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP023Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP023Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP023Rounded2575]

def corrSecondN02701PlusPointP024Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP024Radius2575 : ℝ := ((1100278698883 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701PlusPointP024RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP024Factor2575
        corrSecondN02701PlusPointP024Center2575) =
        corrSecondN02701PlusPointP024Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP024RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP024Rounded2575‖ ≤
          corrSecondN02701PlusPointP024Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP024Factor2575
      corrSecondN02701PlusPointP024Center2575)
  rw [corrSecondN02701PlusPointP024RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP024Factor2575 * embedPair2542
        corrSecondN02701PlusPointP024Center2575)
    (embedPair2542 corrSecondN02701PlusPointP024Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP024DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP024Factor2575,
      corrSecondN02701PlusPointP024Error2575, rounding2542,
      corrSecondN02701PlusPointP024Radius2575]

theorem corrSecondN02701PlusPointP024DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP024Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP024RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP024Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP024Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP024Rounded2575]

def corrSecondN02701PlusPointP025Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP025Radius2575 : ℝ := ((2200557398033 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701PlusPointP025RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP025Factor2575
        corrSecondN02701PlusPointP025Center2575) =
        corrSecondN02701PlusPointP025Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP025RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP025Rounded2575‖ ≤
          corrSecondN02701PlusPointP025Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP025Factor2575
      corrSecondN02701PlusPointP025Center2575)
  rw [corrSecondN02701PlusPointP025RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP025Factor2575 * embedPair2542
        corrSecondN02701PlusPointP025Center2575)
    (embedPair2542 corrSecondN02701PlusPointP025Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP025DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP025Factor2575,
      corrSecondN02701PlusPointP025Error2575, rounding2542,
      corrSecondN02701PlusPointP025Radius2575]

theorem corrSecondN02701PlusPointP025DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP025Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP025RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP025Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP025Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP025Rounded2575]

def corrSecondN02701PlusPointP026Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP026Radius2575 : ℝ := ((1100278699153 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

theorem corrSecondN02701PlusPointP026RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP026Factor2575
        corrSecondN02701PlusPointP026Center2575) =
        corrSecondN02701PlusPointP026Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP026RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP026Rounded2575‖ ≤
          corrSecondN02701PlusPointP026Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP026Factor2575
      corrSecondN02701PlusPointP026Center2575)
  rw [corrSecondN02701PlusPointP026RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP026Factor2575 * embedPair2542
        corrSecondN02701PlusPointP026Center2575)
    (embedPair2542 corrSecondN02701PlusPointP026Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP026DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP026Factor2575,
      corrSecondN02701PlusPointP026Error2575, rounding2542,
      corrSecondN02701PlusPointP026Radius2575]

theorem corrSecondN02701PlusPointP026DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP026Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP026RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP026Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP026Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP026Rounded2575]

def corrSecondN02701PlusPointP027Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP027Radius2575 : ℝ := ((2200557398699 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701PlusPointP027RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP027Factor2575
        corrSecondN02701PlusPointP027Center2575) =
        corrSecondN02701PlusPointP027Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP027RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP027Rounded2575‖ ≤
          corrSecondN02701PlusPointP027Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP027Factor2575
      corrSecondN02701PlusPointP027Center2575)
  rw [corrSecondN02701PlusPointP027RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP027Factor2575 * embedPair2542
        corrSecondN02701PlusPointP027Center2575)
    (embedPair2542 corrSecondN02701PlusPointP027Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP027DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP027Factor2575,
      corrSecondN02701PlusPointP027Error2575, rounding2542,
      corrSecondN02701PlusPointP027Radius2575]

theorem corrSecondN02701PlusPointP027DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP027Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP027RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP027Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP027Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP027Rounded2575]

def corrSecondN02701PlusPointP028Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP028Radius2575 : ℝ := ((2200557398855 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem corrSecondN02701PlusPointP028RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP028Factor2575
        corrSecondN02701PlusPointP028Center2575) =
        corrSecondN02701PlusPointP028Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP028RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP028Rounded2575‖ ≤
          corrSecondN02701PlusPointP028Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP028Factor2575
      corrSecondN02701PlusPointP028Center2575)
  rw [corrSecondN02701PlusPointP028RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP028Factor2575 * embedPair2542
        corrSecondN02701PlusPointP028Center2575)
    (embedPair2542 corrSecondN02701PlusPointP028Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP028DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP028Factor2575,
      corrSecondN02701PlusPointP028Error2575, rounding2542,
      corrSecondN02701PlusPointP028Radius2575]

theorem corrSecondN02701PlusPointP028DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP028Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP028RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP028Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP028Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP028Rounded2575]

def corrSecondN02701PlusPointP029Rounded2575 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def corrSecondN02701PlusPointP029Radius2575 : ℝ := ((550139349773 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

theorem corrSecondN02701PlusPointP029RoundCompute2575 :
    pairRound2542 (pairMul2542 corrSecondN02701PlusPointP029Factor2575
        corrSecondN02701PlusPointP029Center2575) =
        corrSecondN02701PlusPointP029Rounded2575 := by
  cbv

theorem corrSecondN02701PlusPointP029RoundedError2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02701PlusPointPosition2575 -
      embedPair2542 corrSecondN02701PlusPointP029Rounded2575‖ ≤
          corrSecondN02701PlusPointP029Radius2575 := by
  have hr := embedPair_round_error2542 (pairMul2542 corrSecondN02701PlusPointP029Factor2575
      corrSecondN02701PlusPointP029Center2575)
  rw [corrSecondN02701PlusPointP029RoundCompute2575, embedPair_mul2542] at hr
  have h := (corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP029Factor2575 * embedPair2542
        corrSecondN02701PlusPointP029Center2575)
    (embedPair2542 corrSecondN02701PlusPointP029Rounded2575)).trans (add_le_add
        corrSecondN02701PlusPointP029DerivativeError2575 hr)
  apply h.trans
  norm_num [pairMagnitude2542, corrSecondN02701PlusPointP029Factor2575,
      corrSecondN02701PlusPointP029Error2575, rounding2542,
      corrSecondN02701PlusPointP029Radius2575]

theorem corrSecondN02701PlusPointP029DerivativeNorm2575 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02701PlusPointPosition2575‖ ≤ 1 := by
  have h := corrSecondN02701PlusPoint_triangle2575
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        corrSecondN02701PlusPointPosition2575)
    (embedPair2542 corrSecondN02701PlusPointP029Rounded2575) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add corrSecondN02701PlusPointP029RoundedError2575
      (embedPair_magnitude2542
      corrSecondN02701PlusPointP029Rounded2575))
  apply h'.trans
  norm_num [corrSecondN02701PlusPointP029Radius2575, pairMagnitude2542,
      corrSecondN02701PlusPointP029Rounded2575]

noncomputable def corrSecondN02701PlusSignedValue2575 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 corrSecondN02701PlusPointP000Rounded2575
  | 1 => embedPair2542 corrSecondN02701PlusPointP001Rounded2575
  | 2 => embedPair2542 corrSecondN02701PlusPointP002Rounded2575
  | 3 => embedPair2542 corrSecondN02701PlusPointP003Rounded2575
  | 4 => embedPair2542 corrSecondN02701PlusPointP004Rounded2575
  | 5 => embedPair2542 corrSecondN02701PlusPointP005Rounded2575
  | 6 => embedPair2542 corrSecondN02701PlusPointP006Rounded2575
  | 7 => embedPair2542 corrSecondN02701PlusPointP007Rounded2575
  | 8 => embedPair2542 corrSecondN02701PlusPointP008Rounded2575
  | 9 => embedPair2542 corrSecondN02701PlusPointP009Rounded2575
  | 10 => embedPair2542 corrSecondN02701PlusPointP010Rounded2575
  | 11 => embedPair2542 corrSecondN02701PlusPointP011Rounded2575
  | 12 => embedPair2542 corrSecondN02701PlusPointP012Rounded2575
  | 13 => embedPair2542 corrSecondN02701PlusPointP013Rounded2575
  | 14 => embedPair2542 corrSecondN02701PlusPointP014Rounded2575
  | 15 => embedPair2542 corrSecondN02701PlusPointP015Rounded2575
  | 16 => embedPair2542 corrSecondN02701PlusPointP016Rounded2575
  | 17 => embedPair2542 corrSecondN02701PlusPointP017Rounded2575
  | 18 => embedPair2542 corrSecondN02701PlusPointP018Rounded2575
  | 19 => embedPair2542 corrSecondN02701PlusPointP019Rounded2575
  | 20 => embedPair2542 corrSecondN02701PlusPointP020Rounded2575
  | 21 => embedPair2542 corrSecondN02701PlusPointP021Rounded2575
  | 22 => embedPair2542 corrSecondN02701PlusPointP022Rounded2575
  | 23 => embedPair2542 corrSecondN02701PlusPointP023Rounded2575
  | 24 => embedPair2542 corrSecondN02701PlusPointP024Rounded2575
  | 25 => embedPair2542 corrSecondN02701PlusPointP025Rounded2575
  | 26 => embedPair2542 corrSecondN02701PlusPointP026Rounded2575
  | 27 => embedPair2542 corrSecondN02701PlusPointP027Rounded2575
  | 28 => embedPair2542 corrSecondN02701PlusPointP028Rounded2575
  | 29 => embedPair2542 corrSecondN02701PlusPointP029Rounded2575
  | _ => 0

noncomputable def corrSecondN02701PlusSignedError2575 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => corrSecondN02701PlusPointP000Radius2575
  | 1 => corrSecondN02701PlusPointP001Radius2575
  | 2 => corrSecondN02701PlusPointP002Radius2575
  | 3 => corrSecondN02701PlusPointP003Radius2575
  | 4 => corrSecondN02701PlusPointP004Radius2575
  | 5 => corrSecondN02701PlusPointP005Radius2575
  | 6 => corrSecondN02701PlusPointP006Radius2575
  | 7 => corrSecondN02701PlusPointP007Radius2575
  | 8 => corrSecondN02701PlusPointP008Radius2575
  | 9 => corrSecondN02701PlusPointP009Radius2575
  | 10 => corrSecondN02701PlusPointP010Radius2575
  | 11 => corrSecondN02701PlusPointP011Radius2575
  | 12 => corrSecondN02701PlusPointP012Radius2575
  | 13 => corrSecondN02701PlusPointP013Radius2575
  | 14 => corrSecondN02701PlusPointP014Radius2575
  | 15 => corrSecondN02701PlusPointP015Radius2575
  | 16 => corrSecondN02701PlusPointP016Radius2575
  | 17 => corrSecondN02701PlusPointP017Radius2575
  | 18 => corrSecondN02701PlusPointP018Radius2575
  | 19 => corrSecondN02701PlusPointP019Radius2575
  | 20 => corrSecondN02701PlusPointP020Radius2575
  | 21 => corrSecondN02701PlusPointP021Radius2575
  | 22 => corrSecondN02701PlusPointP022Radius2575
  | 23 => corrSecondN02701PlusPointP023Radius2575
  | 24 => corrSecondN02701PlusPointP024Radius2575
  | 25 => corrSecondN02701PlusPointP025Radius2575
  | 26 => corrSecondN02701PlusPointP026Radius2575
  | 27 => corrSecondN02701PlusPointP027Radius2575
  | 28 => corrSecondN02701PlusPointP028Radius2575
  | 29 => corrSecondN02701PlusPointP029Radius2575
  | _ => 0

theorem corrSecondN02701PlusSignedExpError2575 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrSecondN02701PlusPointPosition2575 -
        corrSecondN02701PlusSignedValue2575 i‖ ≤ corrSecondN02701PlusSignedError2575 i := by
  fin_cases i
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP000RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP001RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP002RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP003RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP004RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP005RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP006RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP007RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP008RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP009RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP010RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP011RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP012RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP013RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP014RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP015RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP016RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP017RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP018RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP019RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP020RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP021RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP022RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP023RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP024RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP025RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP026RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP027RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP028RoundedError2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP029RoundedError2575

theorem corrSecondN02701PlusSignedUnitNorm2575 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrSecondN02701PlusPointPosition2575‖ ≤ 1
        := by
  fin_cases i
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP000DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP001DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP002DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP003DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP004DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP005DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP006DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP007DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP008DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP009DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP010DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP011DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP012DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP013DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP014DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP015DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP016DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP017DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP018DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP019DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP020DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP021DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP022DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP023DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP024DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP025DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP026DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP027DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP028DerivativeNorm2575
  · simpa only [corrSecondN02701PlusSignedValue2575, corrSecondN02701PlusSignedError2575] using
      corrSecondN02701PlusPointP029DerivativeNorm2575

noncomputable def corrSecondN02701PlusSignedSum2575 : ℂ := ⟨(((-(((1507874419245 * 10^40
        + 5945010752003448176198141747494458440311) * 10^40
        + 4718324215364854654079196128254894864209) * 10^40
        + 4197548237041839531115281225575386081609)) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888)),
    (((((509033367438 * 10^40
        + 3507512159837972314337210193448527496506) * 10^40
        + 1645319615077192032517682144179221481184) * 10^40
        + 9938045989703618571653065017409060867469) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888))⟩

noncomputable def corrSecondN02701PlusSignedUpper2575 : ℝ := ((56053459 : ℝ) /
        50000000)

theorem corrSecondN02701PlusSignedSum_eq2575 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSecondN02701PlusSignedValue2575 i) =
      corrSecondN02701PlusSignedSum2575 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        corrSecondN02701PlusSignedValue2575,
      corrSecondN02701PlusSignedSum2575, embedPair2542, corrSecondN02701PlusPointP000Rounded2575,
      corrSecondN02701PlusPointP001Rounded2575,
      corrSecondN02701PlusPointP002Rounded2575,
      corrSecondN02701PlusPointP003Rounded2575,
      corrSecondN02701PlusPointP004Rounded2575,
      corrSecondN02701PlusPointP005Rounded2575,
      corrSecondN02701PlusPointP006Rounded2575,
      corrSecondN02701PlusPointP007Rounded2575,
      corrSecondN02701PlusPointP008Rounded2575,
      corrSecondN02701PlusPointP009Rounded2575,
      corrSecondN02701PlusPointP010Rounded2575,
      corrSecondN02701PlusPointP011Rounded2575,
      corrSecondN02701PlusPointP012Rounded2575,
      corrSecondN02701PlusPointP013Rounded2575,
      corrSecondN02701PlusPointP014Rounded2575,
      corrSecondN02701PlusPointP015Rounded2575,
      corrSecondN02701PlusPointP016Rounded2575,
      corrSecondN02701PlusPointP017Rounded2575,
      corrSecondN02701PlusPointP018Rounded2575,
      corrSecondN02701PlusPointP019Rounded2575,
      corrSecondN02701PlusPointP020Rounded2575,
      corrSecondN02701PlusPointP021Rounded2575,
      corrSecondN02701PlusPointP022Rounded2575,
      corrSecondN02701PlusPointP023Rounded2575,
      corrSecondN02701PlusPointP024Rounded2575,
      corrSecondN02701PlusPointP025Rounded2575,
      corrSecondN02701PlusPointP026Rounded2575,
      corrSecondN02701PlusPointP027Rounded2575,
      corrSecondN02701PlusPointP028Rounded2575,
      corrSecondN02701PlusPointP029Rounded2575, Complex.mul_re, Complex.mul_im]

theorem corrSecondN02701PlusSignedSum_norm2575 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSecondN02701PlusSignedValue2575 i‖ ≤
        ((28026727 :
        ℝ) /
        25000000) := by
  rw [corrSecondN02701PlusSignedSum_eq2575]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [corrSecondN02701PlusSignedSum2575]

theorem corrSecondN02701PlusSignedCharge2575 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * corrSecondN02701PlusSignedError2575 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      corrSecondN02701PlusSignedError2575, corrSecondN02701PlusPointP000Radius2575,
      corrSecondN02701PlusPointP001Radius2575,
      corrSecondN02701PlusPointP002Radius2575,
      corrSecondN02701PlusPointP003Radius2575,
      corrSecondN02701PlusPointP004Radius2575,
      corrSecondN02701PlusPointP005Radius2575,
      corrSecondN02701PlusPointP006Radius2575,
      corrSecondN02701PlusPointP007Radius2575,
      corrSecondN02701PlusPointP008Radius2575,
      corrSecondN02701PlusPointP009Radius2575,
      corrSecondN02701PlusPointP010Radius2575,
      corrSecondN02701PlusPointP011Radius2575,
      corrSecondN02701PlusPointP012Radius2575,
      corrSecondN02701PlusPointP013Radius2575,
      corrSecondN02701PlusPointP014Radius2575,
      corrSecondN02701PlusPointP015Radius2575,
      corrSecondN02701PlusPointP016Radius2575,
      corrSecondN02701PlusPointP017Radius2575,
      corrSecondN02701PlusPointP018Radius2575,
      corrSecondN02701PlusPointP019Radius2575,
      corrSecondN02701PlusPointP020Radius2575,
      corrSecondN02701PlusPointP021Radius2575,
      corrSecondN02701PlusPointP022Radius2575,
      corrSecondN02701PlusPointP023Radius2575,
      corrSecondN02701PlusPointP024Radius2575,
      corrSecondN02701PlusPointP025Radius2575,
      corrSecondN02701PlusPointP026Radius2575,
      corrSecondN02701PlusPointP027Radius2575,
      corrSecondN02701PlusPointP028Radius2575,
      corrSecondN02701PlusPointP029Radius2575]

theorem corrSecondN02701PlusSignedUpper_le2575 :
    signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 corrSecondN02701PlusPointPosition2575 ≤
          corrSecondN02701PlusSignedUpper2575 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrSecondN02701PlusPointPosition2575‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSecondN02701PlusSignedValue2575 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * corrSecondN02701PlusSignedError2575 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (corrSecondN02701PlusSignedExpError2575
        i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrSecondN02701PlusPointPosition2575‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (corrSecondN02701PlusSignedUnitNorm2575 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i corrSecondN02701PlusPointPosition2575‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 corrSecondN02701PlusSignedUpper2575
  linarith [corrSecondN02701PlusSignedSum_norm2575, corrSecondN02701PlusSignedCharge2575]

theorem corrSecondN02701PlusPhysical2575 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        corrSecondN02701PlusPointPosition2575‖ ≤
      corrSecondN02701PlusSignedUpper2575 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        corrSecondN02701PlusPointPosition2575
  exact h.trans corrSecondN02701PlusSignedUpper_le2575

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusSignedExpError2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusSignedSum_eq2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusSignedCharge2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusSignedUpper_le2575
#print axioms ConnesWeilRH.Dev.corrSecondN02701PlusPhysical2575
