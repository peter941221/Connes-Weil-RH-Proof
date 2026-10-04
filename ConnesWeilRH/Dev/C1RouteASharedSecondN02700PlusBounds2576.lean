import ConnesWeilRH.Dev.C1RouteASharedSecondN02700PlusDerivatives2576
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators

theorem sharedSecondN02700PlusPoint_triangle2576 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

def sharedSecondN02700PlusPointP000Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP000Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP000RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP000Factor2576
        sharedSecondN02700PlusPointP000Center2576) =
        sharedSecondN02700PlusPointP000Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP000RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP000Rounded2576‖ ≤
          sharedSecondN02700PlusPointP000Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP000Factor2576
      sharedSecondN02700PlusPointP000Center2576)
  rw [sharedSecondN02700PlusPointP000RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP000Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP000Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP000Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP000DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP000Factor2576,
      sharedSecondN02700PlusPointP000Error2576, rounding2542,
      sharedSecondN02700PlusPointP000Radius2576]

theorem sharedSecondN02700PlusPointP000DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP000Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP000RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP000Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP000Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP000Rounded2576]

def sharedSecondN02700PlusPointP001Rounded2576 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP001Radius2576 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02700PlusPointP001RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP001Factor2576
        sharedSecondN02700PlusPointP001Center2576) =
        sharedSecondN02700PlusPointP001Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP001RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP001Rounded2576‖ ≤
          sharedSecondN02700PlusPointP001Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP001Factor2576
      sharedSecondN02700PlusPointP001Center2576)
  rw [sharedSecondN02700PlusPointP001RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP001Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP001Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP001Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP001DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP001Factor2576,
      sharedSecondN02700PlusPointP001Error2576, rounding2542,
      sharedSecondN02700PlusPointP001Radius2576]

theorem sharedSecondN02700PlusPointP001DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP001Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP001RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP001Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP001Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP001Rounded2576]

def sharedSecondN02700PlusPointP002Rounded2576 : RatPair2542 :=
  (((319595 : ℚ) /
        316912650057057350374175801344),
    (((-1056677) : ℚ) /
        1267650600228229401496703205376))

noncomputable def sharedSecondN02700PlusPointP002Radius2576 : ℝ := ((2199023262001 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02700PlusPointP002RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP002Factor2576
        sharedSecondN02700PlusPointP002Center2576) =
        sharedSecondN02700PlusPointP002Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP002RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP002Rounded2576‖ ≤
          sharedSecondN02700PlusPointP002Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP002Factor2576
      sharedSecondN02700PlusPointP002Center2576)
  rw [sharedSecondN02700PlusPointP002RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP002Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP002Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP002Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP002DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP002Factor2576,
      sharedSecondN02700PlusPointP002Error2576, rounding2542,
      sharedSecondN02700PlusPointP002Radius2576]

theorem sharedSecondN02700PlusPointP002DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP002Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP002RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP002Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP002Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP002Rounded2576]

def sharedSecondN02700PlusPointP003Rounded2576 : RatPair2542 :=
  (((15395583093801 : ℚ) /
        1267650600228229401496703205376),
    ((3375515622365 : ℚ) /
        1267650600228229401496703205376))

noncomputable def sharedSecondN02700PlusPointP003Radius2576 : ℝ := ((2276012570833 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02700PlusPointP003RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP003Factor2576
        sharedSecondN02700PlusPointP003Center2576) =
        sharedSecondN02700PlusPointP003Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP003RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP003Rounded2576‖ ≤
          sharedSecondN02700PlusPointP003Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP003Factor2576
      sharedSecondN02700PlusPointP003Center2576)
  rw [sharedSecondN02700PlusPointP003RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP003Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP003Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP003Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP003DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP003Factor2576,
      sharedSecondN02700PlusPointP003Error2576, rounding2542,
      sharedSecondN02700PlusPointP003Radius2576]

theorem sharedSecondN02700PlusPointP003DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP003Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP003RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP003Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP003Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP003Rounded2576]

def sharedSecondN02700PlusPointP004Rounded2576 : RatPair2542 :=
  (((3081881776893327 : ℚ) /
        633825300114114700748351602688),
    (((-3768077214936263) : ℚ) /
        1267650600228229401496703205376))

noncomputable def sharedSecondN02700PlusPointP004Radius2576 : ℝ := ((33988247501147 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02700PlusPointP004RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP004Factor2576
        sharedSecondN02700PlusPointP004Center2576) =
        sharedSecondN02700PlusPointP004Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP004RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP004Rounded2576‖ ≤
          sharedSecondN02700PlusPointP004Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP004Factor2576
      sharedSecondN02700PlusPointP004Center2576)
  rw [sharedSecondN02700PlusPointP004RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP004Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP004Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP004Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP004DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP004Factor2576,
      sharedSecondN02700PlusPointP004Error2576, rounding2542,
      sharedSecondN02700PlusPointP004Radius2576]

theorem sharedSecondN02700PlusPointP004DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP004Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP004RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP004Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP004Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP004Rounded2576]

def sharedSecondN02700PlusPointP005Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP005Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP005RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP005Factor2576
        sharedSecondN02700PlusPointP005Center2576) =
        sharedSecondN02700PlusPointP005Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP005RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP005Rounded2576‖ ≤
          sharedSecondN02700PlusPointP005Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP005Factor2576
      sharedSecondN02700PlusPointP005Center2576)
  rw [sharedSecondN02700PlusPointP005RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP005Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP005Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP005Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP005DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP005Factor2576,
      sharedSecondN02700PlusPointP005Error2576, rounding2542,
      sharedSecondN02700PlusPointP005Radius2576]

theorem sharedSecondN02700PlusPointP005DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP005Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP005RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP005Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP005Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP005Rounded2576]

def sharedSecondN02700PlusPointP006Rounded2576 : RatPair2542 :=
  (((3 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP006Radius2576 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02700PlusPointP006RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP006Factor2576
        sharedSecondN02700PlusPointP006Center2576) =
        sharedSecondN02700PlusPointP006Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP006RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP006Rounded2576‖ ≤
          sharedSecondN02700PlusPointP006Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP006Factor2576
      sharedSecondN02700PlusPointP006Center2576)
  rw [sharedSecondN02700PlusPointP006RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP006Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP006Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP006Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP006DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP006Factor2576,
      sharedSecondN02700PlusPointP006Error2576, rounding2542,
      sharedSecondN02700PlusPointP006Radius2576]

theorem sharedSecondN02700PlusPointP006DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP006Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP006RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP006Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP006Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP006Rounded2576]

def sharedSecondN02700PlusPointP007Rounded2576 : RatPair2542 :=
  (((1837429076517 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP007Radius2576 : ℝ := ((2199290244015 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem sharedSecondN02700PlusPointP007RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP007Factor2576
        sharedSecondN02700PlusPointP007Center2576) =
        sharedSecondN02700PlusPointP007Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP007RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP007Rounded2576‖ ≤
          sharedSecondN02700PlusPointP007Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP007Factor2576
      sharedSecondN02700PlusPointP007Center2576)
  rw [sharedSecondN02700PlusPointP007RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP007Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP007Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP007Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP007DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP007Factor2576,
      sharedSecondN02700PlusPointP007Error2576, rounding2542,
      sharedSecondN02700PlusPointP007Radius2576]

theorem sharedSecondN02700PlusPointP007DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP007Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP007RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP007Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP007Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP007Rounded2576]

def sharedSecondN02700PlusPointP008Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP008Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP008RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP008Factor2576
        sharedSecondN02700PlusPointP008Center2576) =
        sharedSecondN02700PlusPointP008Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP008RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP008Rounded2576‖ ≤
          sharedSecondN02700PlusPointP008Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP008Factor2576
      sharedSecondN02700PlusPointP008Center2576)
  rw [sharedSecondN02700PlusPointP008RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP008Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP008Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP008Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP008DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP008Factor2576,
      sharedSecondN02700PlusPointP008Error2576, rounding2542,
      sharedSecondN02700PlusPointP008Radius2576]

theorem sharedSecondN02700PlusPointP008DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP008Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP008RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP008Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP008Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP008Rounded2576]

def sharedSecondN02700PlusPointP009Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP009Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP009RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP009Factor2576
        sharedSecondN02700PlusPointP009Center2576) =
        sharedSecondN02700PlusPointP009Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP009RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP009Rounded2576‖ ≤
          sharedSecondN02700PlusPointP009Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP009Factor2576
      sharedSecondN02700PlusPointP009Center2576)
  rw [sharedSecondN02700PlusPointP009RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP009Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP009Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP009Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP009DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP009Factor2576,
      sharedSecondN02700PlusPointP009Error2576, rounding2542,
      sharedSecondN02700PlusPointP009Radius2576]

theorem sharedSecondN02700PlusPointP009DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP009Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP009RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP009Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP009Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP009Rounded2576]

def sharedSecondN02700PlusPointP010Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP010Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP010RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP010Factor2576
        sharedSecondN02700PlusPointP010Center2576) =
        sharedSecondN02700PlusPointP010Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP010RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP010Rounded2576‖ ≤
          sharedSecondN02700PlusPointP010Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP010Factor2576
      sharedSecondN02700PlusPointP010Center2576)
  rw [sharedSecondN02700PlusPointP010RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP010Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP010Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP010Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP010DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP010Factor2576,
      sharedSecondN02700PlusPointP010Error2576, rounding2542,
      sharedSecondN02700PlusPointP010Radius2576]

theorem sharedSecondN02700PlusPointP010DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP010Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP010RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP010Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP010Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP010Rounded2576]

def sharedSecondN02700PlusPointP011Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP011Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP011RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP011Factor2576
        sharedSecondN02700PlusPointP011Center2576) =
        sharedSecondN02700PlusPointP011Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP011RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP011Rounded2576‖ ≤
          sharedSecondN02700PlusPointP011Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP011Factor2576
      sharedSecondN02700PlusPointP011Center2576)
  rw [sharedSecondN02700PlusPointP011RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP011Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP011Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP011Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP011DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP011Factor2576,
      sharedSecondN02700PlusPointP011Error2576, rounding2542,
      sharedSecondN02700PlusPointP011Radius2576]

theorem sharedSecondN02700PlusPointP011DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP011Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP011RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP011Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP011Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP011Rounded2576]

def sharedSecondN02700PlusPointP012Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP012Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP012RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP012Factor2576
        sharedSecondN02700PlusPointP012Center2576) =
        sharedSecondN02700PlusPointP012Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP012RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP012Rounded2576‖ ≤
          sharedSecondN02700PlusPointP012Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP012Factor2576
      sharedSecondN02700PlusPointP012Center2576)
  rw [sharedSecondN02700PlusPointP012RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP012Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP012Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP012Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP012DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP012Factor2576,
      sharedSecondN02700PlusPointP012Error2576, rounding2542,
      sharedSecondN02700PlusPointP012Radius2576]

theorem sharedSecondN02700PlusPointP012DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP012Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP012RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP012Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP012Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP012Rounded2576]

def sharedSecondN02700PlusPointP013Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP013Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP013RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP013Factor2576
        sharedSecondN02700PlusPointP013Center2576) =
        sharedSecondN02700PlusPointP013Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP013RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP013Rounded2576‖ ≤
          sharedSecondN02700PlusPointP013Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP013Factor2576
      sharedSecondN02700PlusPointP013Center2576)
  rw [sharedSecondN02700PlusPointP013RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP013Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP013Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP013Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP013DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP013Factor2576,
      sharedSecondN02700PlusPointP013Error2576, rounding2542,
      sharedSecondN02700PlusPointP013Radius2576]

theorem sharedSecondN02700PlusPointP013DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP013Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP013RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP013Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP013Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP013Rounded2576]

def sharedSecondN02700PlusPointP014Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP014Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP014RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP014Factor2576
        sharedSecondN02700PlusPointP014Center2576) =
        sharedSecondN02700PlusPointP014Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP014RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP014Rounded2576‖ ≤
          sharedSecondN02700PlusPointP014Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP014Factor2576
      sharedSecondN02700PlusPointP014Center2576)
  rw [sharedSecondN02700PlusPointP014RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP014Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP014Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP014Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP014DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP014Factor2576,
      sharedSecondN02700PlusPointP014Error2576, rounding2542,
      sharedSecondN02700PlusPointP014Radius2576]

theorem sharedSecondN02700PlusPointP014DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP014Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP014RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP014Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP014Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP014Rounded2576]

def sharedSecondN02700PlusPointP015Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP015Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP015RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP015Factor2576
        sharedSecondN02700PlusPointP015Center2576) =
        sharedSecondN02700PlusPointP015Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP015RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP015Rounded2576‖ ≤
          sharedSecondN02700PlusPointP015Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP015Factor2576
      sharedSecondN02700PlusPointP015Center2576)
  rw [sharedSecondN02700PlusPointP015RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP015Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP015Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP015Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP015DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP015Factor2576,
      sharedSecondN02700PlusPointP015Error2576, rounding2542,
      sharedSecondN02700PlusPointP015Radius2576]

theorem sharedSecondN02700PlusPointP015DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP015Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP015RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP015Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP015Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP015Rounded2576]

def sharedSecondN02700PlusPointP016Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP016Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP016RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP016Factor2576
        sharedSecondN02700PlusPointP016Center2576) =
        sharedSecondN02700PlusPointP016Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP016RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP016Rounded2576‖ ≤
          sharedSecondN02700PlusPointP016Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP016Factor2576
      sharedSecondN02700PlusPointP016Center2576)
  rw [sharedSecondN02700PlusPointP016RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP016Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP016Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP016Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP016DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP016Factor2576,
      sharedSecondN02700PlusPointP016Error2576, rounding2542,
      sharedSecondN02700PlusPointP016Radius2576]

theorem sharedSecondN02700PlusPointP016DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP016Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP016RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP016Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP016Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP016Rounded2576]

def sharedSecondN02700PlusPointP017Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP017Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP017RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP017Factor2576
        sharedSecondN02700PlusPointP017Center2576) =
        sharedSecondN02700PlusPointP017Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP017RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP017Rounded2576‖ ≤
          sharedSecondN02700PlusPointP017Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP017Factor2576
      sharedSecondN02700PlusPointP017Center2576)
  rw [sharedSecondN02700PlusPointP017RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP017Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP017Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP017Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP017DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP017Factor2576,
      sharedSecondN02700PlusPointP017Error2576, rounding2542,
      sharedSecondN02700PlusPointP017Radius2576]

theorem sharedSecondN02700PlusPointP017DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP017Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP017RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP017Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP017Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP017Rounded2576]

def sharedSecondN02700PlusPointP018Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP018Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP018RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP018Factor2576
        sharedSecondN02700PlusPointP018Center2576) =
        sharedSecondN02700PlusPointP018Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP018RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP018Rounded2576‖ ≤
          sharedSecondN02700PlusPointP018Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP018Factor2576
      sharedSecondN02700PlusPointP018Center2576)
  rw [sharedSecondN02700PlusPointP018RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP018Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP018Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP018Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP018DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP018Factor2576,
      sharedSecondN02700PlusPointP018Error2576, rounding2542,
      sharedSecondN02700PlusPointP018Radius2576]

theorem sharedSecondN02700PlusPointP018DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP018Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP018RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP018Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP018Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP018Rounded2576]

def sharedSecondN02700PlusPointP019Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP019Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP019RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP019Factor2576
        sharedSecondN02700PlusPointP019Center2576) =
        sharedSecondN02700PlusPointP019Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP019RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP019Rounded2576‖ ≤
          sharedSecondN02700PlusPointP019Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP019Factor2576
      sharedSecondN02700PlusPointP019Center2576)
  rw [sharedSecondN02700PlusPointP019RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP019Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP019Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP019Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP019DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP019Factor2576,
      sharedSecondN02700PlusPointP019Error2576, rounding2542,
      sharedSecondN02700PlusPointP019Radius2576]

theorem sharedSecondN02700PlusPointP019DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP019Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP019RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP019Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP019Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP019Rounded2576]

def sharedSecondN02700PlusPointP020Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP020Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP020RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP020Factor2576
        sharedSecondN02700PlusPointP020Center2576) =
        sharedSecondN02700PlusPointP020Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP020RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP020Rounded2576‖ ≤
          sharedSecondN02700PlusPointP020Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP020Factor2576
      sharedSecondN02700PlusPointP020Center2576)
  rw [sharedSecondN02700PlusPointP020RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP020Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP020Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP020Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP020DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP020Factor2576,
      sharedSecondN02700PlusPointP020Error2576, rounding2542,
      sharedSecondN02700PlusPointP020Radius2576]

theorem sharedSecondN02700PlusPointP020DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP020Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP020RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP020Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP020Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP020Rounded2576]

def sharedSecondN02700PlusPointP021Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP021Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP021RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP021Factor2576
        sharedSecondN02700PlusPointP021Center2576) =
        sharedSecondN02700PlusPointP021Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP021RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP021Rounded2576‖ ≤
          sharedSecondN02700PlusPointP021Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP021Factor2576
      sharedSecondN02700PlusPointP021Center2576)
  rw [sharedSecondN02700PlusPointP021RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP021Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP021Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP021Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP021DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP021Factor2576,
      sharedSecondN02700PlusPointP021Error2576, rounding2542,
      sharedSecondN02700PlusPointP021Radius2576]

theorem sharedSecondN02700PlusPointP021DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP021Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP021RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP021Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP021Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP021Rounded2576]

def sharedSecondN02700PlusPointP022Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP022Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP022RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP022Factor2576
        sharedSecondN02700PlusPointP022Center2576) =
        sharedSecondN02700PlusPointP022Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP022RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP022Rounded2576‖ ≤
          sharedSecondN02700PlusPointP022Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP022Factor2576
      sharedSecondN02700PlusPointP022Center2576)
  rw [sharedSecondN02700PlusPointP022RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP022Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP022Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP022Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP022DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP022Factor2576,
      sharedSecondN02700PlusPointP022Error2576, rounding2542,
      sharedSecondN02700PlusPointP022Radius2576]

theorem sharedSecondN02700PlusPointP022DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP022Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP022RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP022Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP022Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP022Rounded2576]

def sharedSecondN02700PlusPointP023Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP023Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP023RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP023Factor2576
        sharedSecondN02700PlusPointP023Center2576) =
        sharedSecondN02700PlusPointP023Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP023RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP023Rounded2576‖ ≤
          sharedSecondN02700PlusPointP023Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP023Factor2576
      sharedSecondN02700PlusPointP023Center2576)
  rw [sharedSecondN02700PlusPointP023RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP023Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP023Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP023Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP023DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP023Factor2576,
      sharedSecondN02700PlusPointP023Error2576, rounding2542,
      sharedSecondN02700PlusPointP023Radius2576]

theorem sharedSecondN02700PlusPointP023DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP023Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP023RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP023Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP023Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP023Rounded2576]

def sharedSecondN02700PlusPointP024Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP024Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP024RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP024Factor2576
        sharedSecondN02700PlusPointP024Center2576) =
        sharedSecondN02700PlusPointP024Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP024RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP024Rounded2576‖ ≤
          sharedSecondN02700PlusPointP024Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP024Factor2576
      sharedSecondN02700PlusPointP024Center2576)
  rw [sharedSecondN02700PlusPointP024RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP024Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP024Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP024Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP024DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP024Factor2576,
      sharedSecondN02700PlusPointP024Error2576, rounding2542,
      sharedSecondN02700PlusPointP024Radius2576]

theorem sharedSecondN02700PlusPointP024DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP024Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP024RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP024Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP024Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP024Rounded2576]

def sharedSecondN02700PlusPointP025Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP025Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP025RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP025Factor2576
        sharedSecondN02700PlusPointP025Center2576) =
        sharedSecondN02700PlusPointP025Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP025RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP025Rounded2576‖ ≤
          sharedSecondN02700PlusPointP025Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP025Factor2576
      sharedSecondN02700PlusPointP025Center2576)
  rw [sharedSecondN02700PlusPointP025RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP025Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP025Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP025Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP025DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP025Factor2576,
      sharedSecondN02700PlusPointP025Error2576, rounding2542,
      sharedSecondN02700PlusPointP025Radius2576]

theorem sharedSecondN02700PlusPointP025DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP025Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP025RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP025Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP025Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP025Rounded2576]

def sharedSecondN02700PlusPointP026Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP026Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP026RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP026Factor2576
        sharedSecondN02700PlusPointP026Center2576) =
        sharedSecondN02700PlusPointP026Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP026RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP026Rounded2576‖ ≤
          sharedSecondN02700PlusPointP026Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP026Factor2576
      sharedSecondN02700PlusPointP026Center2576)
  rw [sharedSecondN02700PlusPointP026RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP026Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP026Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP026Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP026DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP026Factor2576,
      sharedSecondN02700PlusPointP026Error2576, rounding2542,
      sharedSecondN02700PlusPointP026Radius2576]

theorem sharedSecondN02700PlusPointP026DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP026Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP026RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP026Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP026Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP026Rounded2576]

def sharedSecondN02700PlusPointP027Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP027Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP027RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP027Factor2576
        sharedSecondN02700PlusPointP027Center2576) =
        sharedSecondN02700PlusPointP027Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP027RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP027Rounded2576‖ ≤
          sharedSecondN02700PlusPointP027Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP027Factor2576
      sharedSecondN02700PlusPointP027Center2576)
  rw [sharedSecondN02700PlusPointP027RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP027Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP027Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP027Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP027DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP027Factor2576,
      sharedSecondN02700PlusPointP027Error2576, rounding2542,
      sharedSecondN02700PlusPointP027Radius2576]

theorem sharedSecondN02700PlusPointP027DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP027Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP027RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP027Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP027Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP027Rounded2576]

def sharedSecondN02700PlusPointP028Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP028Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP028RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP028Factor2576
        sharedSecondN02700PlusPointP028Center2576) =
        sharedSecondN02700PlusPointP028Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP028RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP028Rounded2576‖ ≤
          sharedSecondN02700PlusPointP028Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP028Factor2576
      sharedSecondN02700PlusPointP028Center2576)
  rw [sharedSecondN02700PlusPointP028RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP028Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP028Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP028Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP028DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP028Factor2576,
      sharedSecondN02700PlusPointP028Error2576, rounding2542,
      sharedSecondN02700PlusPointP028Radius2576]

theorem sharedSecondN02700PlusPointP028DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP028Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP028RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP028Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP028Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP028Rounded2576]

def sharedSecondN02700PlusPointP029Rounded2576 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def sharedSecondN02700PlusPointP029Radius2576 : ℝ := ((1 : ℝ) /
        633825300114114700748351602688)

theorem sharedSecondN02700PlusPointP029RoundCompute2576 :
    pairRound2542 (pairMul2542 sharedSecondN02700PlusPointP029Factor2576
        sharedSecondN02700PlusPointP029Center2576) =
        sharedSecondN02700PlusPointP029Rounded2576 := by
  cbv

theorem sharedSecondN02700PlusPointP029RoundedError2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02700PlusPointPosition2576 -
      embedPair2542 sharedSecondN02700PlusPointP029Rounded2576‖ ≤
          sharedSecondN02700PlusPointP029Radius2576 := by
  have hr := embedPair_round_error2542 (pairMul2542 sharedSecondN02700PlusPointP029Factor2576
      sharedSecondN02700PlusPointP029Center2576)
  rw [sharedSecondN02700PlusPointP029RoundCompute2576, embedPair_mul2542] at hr
  have h := (sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP029Factor2576 * embedPair2542
        sharedSecondN02700PlusPointP029Center2576)
    (embedPair2542 sharedSecondN02700PlusPointP029Rounded2576)).trans (add_le_add
        sharedSecondN02700PlusPointP029DerivativeError2576 hr)
  apply h.trans
  norm_num [pairMagnitude2542, sharedSecondN02700PlusPointP029Factor2576,
      sharedSecondN02700PlusPointP029Error2576, rounding2542,
      sharedSecondN02700PlusPointP029Radius2576]

theorem sharedSecondN02700PlusPointP029DerivativeNorm2576 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02700PlusPointPosition2576‖ ≤ 1 := by
  have h := sharedSecondN02700PlusPoint_triangle2576
    (weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        sharedSecondN02700PlusPointPosition2576)
    (embedPair2542 sharedSecondN02700PlusPointP029Rounded2576) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add sharedSecondN02700PlusPointP029RoundedError2576
      (embedPair_magnitude2542
      sharedSecondN02700PlusPointP029Rounded2576))
  apply h'.trans
  norm_num [sharedSecondN02700PlusPointP029Radius2576, pairMagnitude2542,
      sharedSecondN02700PlusPointP029Rounded2576]

noncomputable def sharedSecondN02700PlusSignedValue2576 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 sharedSecondN02700PlusPointP000Rounded2576
  | 1 => embedPair2542 sharedSecondN02700PlusPointP001Rounded2576
  | 2 => embedPair2542 sharedSecondN02700PlusPointP002Rounded2576
  | 3 => embedPair2542 sharedSecondN02700PlusPointP003Rounded2576
  | 4 => embedPair2542 sharedSecondN02700PlusPointP004Rounded2576
  | 5 => embedPair2542 sharedSecondN02700PlusPointP005Rounded2576
  | 6 => embedPair2542 sharedSecondN02700PlusPointP006Rounded2576
  | 7 => embedPair2542 sharedSecondN02700PlusPointP007Rounded2576
  | 8 => embedPair2542 sharedSecondN02700PlusPointP008Rounded2576
  | 9 => embedPair2542 sharedSecondN02700PlusPointP009Rounded2576
  | 10 => embedPair2542 sharedSecondN02700PlusPointP010Rounded2576
  | 11 => embedPair2542 sharedSecondN02700PlusPointP011Rounded2576
  | 12 => embedPair2542 sharedSecondN02700PlusPointP012Rounded2576
  | 13 => embedPair2542 sharedSecondN02700PlusPointP013Rounded2576
  | 14 => embedPair2542 sharedSecondN02700PlusPointP014Rounded2576
  | 15 => embedPair2542 sharedSecondN02700PlusPointP015Rounded2576
  | 16 => embedPair2542 sharedSecondN02700PlusPointP016Rounded2576
  | 17 => embedPair2542 sharedSecondN02700PlusPointP017Rounded2576
  | 18 => embedPair2542 sharedSecondN02700PlusPointP018Rounded2576
  | 19 => embedPair2542 sharedSecondN02700PlusPointP019Rounded2576
  | 20 => embedPair2542 sharedSecondN02700PlusPointP020Rounded2576
  | 21 => embedPair2542 sharedSecondN02700PlusPointP021Rounded2576
  | 22 => embedPair2542 sharedSecondN02700PlusPointP022Rounded2576
  | 23 => embedPair2542 sharedSecondN02700PlusPointP023Rounded2576
  | 24 => embedPair2542 sharedSecondN02700PlusPointP024Rounded2576
  | 25 => embedPair2542 sharedSecondN02700PlusPointP025Rounded2576
  | 26 => embedPair2542 sharedSecondN02700PlusPointP026Rounded2576
  | 27 => embedPair2542 sharedSecondN02700PlusPointP027Rounded2576
  | 28 => embedPair2542 sharedSecondN02700PlusPointP028Rounded2576
  | 29 => embedPair2542 sharedSecondN02700PlusPointP029Rounded2576
  | _ => 0

noncomputable def sharedSecondN02700PlusSignedError2576 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => sharedSecondN02700PlusPointP000Radius2576
  | 1 => sharedSecondN02700PlusPointP001Radius2576
  | 2 => sharedSecondN02700PlusPointP002Radius2576
  | 3 => sharedSecondN02700PlusPointP003Radius2576
  | 4 => sharedSecondN02700PlusPointP004Radius2576
  | 5 => sharedSecondN02700PlusPointP005Radius2576
  | 6 => sharedSecondN02700PlusPointP006Radius2576
  | 7 => sharedSecondN02700PlusPointP007Radius2576
  | 8 => sharedSecondN02700PlusPointP008Radius2576
  | 9 => sharedSecondN02700PlusPointP009Radius2576
  | 10 => sharedSecondN02700PlusPointP010Radius2576
  | 11 => sharedSecondN02700PlusPointP011Radius2576
  | 12 => sharedSecondN02700PlusPointP012Radius2576
  | 13 => sharedSecondN02700PlusPointP013Radius2576
  | 14 => sharedSecondN02700PlusPointP014Radius2576
  | 15 => sharedSecondN02700PlusPointP015Radius2576
  | 16 => sharedSecondN02700PlusPointP016Radius2576
  | 17 => sharedSecondN02700PlusPointP017Radius2576
  | 18 => sharedSecondN02700PlusPointP018Radius2576
  | 19 => sharedSecondN02700PlusPointP019Radius2576
  | 20 => sharedSecondN02700PlusPointP020Radius2576
  | 21 => sharedSecondN02700PlusPointP021Radius2576
  | 22 => sharedSecondN02700PlusPointP022Radius2576
  | 23 => sharedSecondN02700PlusPointP023Radius2576
  | 24 => sharedSecondN02700PlusPointP024Radius2576
  | 25 => sharedSecondN02700PlusPointP025Radius2576
  | 26 => sharedSecondN02700PlusPointP026Radius2576
  | 27 => sharedSecondN02700PlusPointP027Radius2576
  | 28 => sharedSecondN02700PlusPointP028Radius2576
  | 29 => sharedSecondN02700PlusPointP029Radius2576
  | _ => 0

theorem sharedSecondN02700PlusSignedExpError2576 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i sharedSecondN02700PlusPointPosition2576 -
        sharedSecondN02700PlusSignedValue2576 i‖ ≤ sharedSecondN02700PlusSignedError2576 i := by
  fin_cases i
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP000RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP001RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP002RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP003RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP004RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP005RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP006RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP007RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP008RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP009RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP010RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP011RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP012RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP013RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP014RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP015RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP016RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP017RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP018RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP019RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP020RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP021RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP022RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP023RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP024RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP025RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP026RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP027RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP028RoundedError2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP029RoundedError2576

theorem sharedSecondN02700PlusSignedUnitNorm2576 (i : Fin 30) :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i sharedSecondN02700PlusPointPosition2576‖ ≤ 1
        := by
  fin_cases i
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP000DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP001DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP002DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP003DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP004DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP005DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP006DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP007DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP008DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP009DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP010DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP011DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP012DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP013DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP014DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP015DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP016DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP017DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP018DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP019DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP020DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP021DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP022DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP023DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP024DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP025DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP026DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP027DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP028DerivativeNorm2576
  · simpa only [sharedSecondN02700PlusSignedValue2576, sharedSecondN02700PlusSignedError2576]
      using
      sharedSecondN02700PlusPointP029DerivativeNorm2576

noncomputable def sharedSecondN02700PlusSignedSum2576 : ℂ := ⟨(((-(((758399844469 * 10^40
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

noncomputable def sharedSecondN02700PlusSignedUpper2576 : ℝ := ((55509237 : ℝ) /
        50000000)

theorem sharedSecondN02700PlusSignedSum_eq2576 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * sharedSecondN02700PlusSignedValue2576 i) =
      sharedSecondN02700PlusSignedSum2576 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        sharedSecondN02700PlusSignedValue2576,
      sharedSecondN02700PlusSignedSum2576, embedPair2542,
          sharedSecondN02700PlusPointP000Rounded2576,
      sharedSecondN02700PlusPointP001Rounded2576,
      sharedSecondN02700PlusPointP002Rounded2576,
      sharedSecondN02700PlusPointP003Rounded2576,
      sharedSecondN02700PlusPointP004Rounded2576,
      sharedSecondN02700PlusPointP005Rounded2576,
      sharedSecondN02700PlusPointP006Rounded2576,
      sharedSecondN02700PlusPointP007Rounded2576,
      sharedSecondN02700PlusPointP008Rounded2576,
      sharedSecondN02700PlusPointP009Rounded2576,
      sharedSecondN02700PlusPointP010Rounded2576,
      sharedSecondN02700PlusPointP011Rounded2576,
      sharedSecondN02700PlusPointP012Rounded2576,
      sharedSecondN02700PlusPointP013Rounded2576,
      sharedSecondN02700PlusPointP014Rounded2576,
      sharedSecondN02700PlusPointP015Rounded2576,
      sharedSecondN02700PlusPointP016Rounded2576,
      sharedSecondN02700PlusPointP017Rounded2576,
      sharedSecondN02700PlusPointP018Rounded2576,
      sharedSecondN02700PlusPointP019Rounded2576,
      sharedSecondN02700PlusPointP020Rounded2576,
      sharedSecondN02700PlusPointP021Rounded2576,
      sharedSecondN02700PlusPointP022Rounded2576,
      sharedSecondN02700PlusPointP023Rounded2576,
      sharedSecondN02700PlusPointP024Rounded2576,
      sharedSecondN02700PlusPointP025Rounded2576,
      sharedSecondN02700PlusPointP026Rounded2576,
      sharedSecondN02700PlusPointP027Rounded2576,
      sharedSecondN02700PlusPointP028Rounded2576,
      sharedSecondN02700PlusPointP029Rounded2576, Complex.mul_re, Complex.mul_im]

theorem sharedSecondN02700PlusSignedSum_norm2576 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * sharedSecondN02700PlusSignedValue2576 i‖ ≤
        ((3469327 : ℝ)
        /
        3125000) := by
  rw [sharedSecondN02700PlusSignedSum_eq2576]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [sharedSecondN02700PlusSignedSum2576]

theorem sharedSecondN02700PlusSignedCharge2576 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * sharedSecondN02700PlusSignedError2576 i) ≤ (1 :
          ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      sharedSecondN02700PlusSignedError2576, sharedSecondN02700PlusPointP000Radius2576,
      sharedSecondN02700PlusPointP001Radius2576,
      sharedSecondN02700PlusPointP002Radius2576,
      sharedSecondN02700PlusPointP003Radius2576,
      sharedSecondN02700PlusPointP004Radius2576,
      sharedSecondN02700PlusPointP005Radius2576,
      sharedSecondN02700PlusPointP006Radius2576,
      sharedSecondN02700PlusPointP007Radius2576,
      sharedSecondN02700PlusPointP008Radius2576,
      sharedSecondN02700PlusPointP009Radius2576,
      sharedSecondN02700PlusPointP010Radius2576,
      sharedSecondN02700PlusPointP011Radius2576,
      sharedSecondN02700PlusPointP012Radius2576,
      sharedSecondN02700PlusPointP013Radius2576,
      sharedSecondN02700PlusPointP014Radius2576,
      sharedSecondN02700PlusPointP015Radius2576,
      sharedSecondN02700PlusPointP016Radius2576,
      sharedSecondN02700PlusPointP017Radius2576,
      sharedSecondN02700PlusPointP018Radius2576,
      sharedSecondN02700PlusPointP019Radius2576,
      sharedSecondN02700PlusPointP020Radius2576,
      sharedSecondN02700PlusPointP021Radius2576,
      sharedSecondN02700PlusPointP022Radius2576,
      sharedSecondN02700PlusPointP023Radius2576,
      sharedSecondN02700PlusPointP024Radius2576,
      sharedSecondN02700PlusPointP025Radius2576,
      sharedSecondN02700PlusPointP026Radius2576,
      sharedSecondN02700PlusPointP027Radius2576,
      sharedSecondN02700PlusPointP028Radius2576,
      sharedSecondN02700PlusPointP029Radius2576]

theorem sharedSecondN02700PlusSignedUpper_le2576 :
    signedJetUpper2539 2 (1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 sharedSecondN02700PlusPointPosition2576 ≤
          sharedSecondN02700PlusSignedUpper2576 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 2 (1/2) nodeModulation2541 i sharedSecondN02700PlusPointPosition2576‖
            ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * sharedSecondN02700PlusSignedValue2576 i‖
          +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * sharedSecondN02700PlusSignedError2576 i :=
              by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _)
        (sharedSecondN02700PlusSignedExpError2576
        i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i sharedSecondN02700PlusPointPosition2576‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (sharedSecondN02700PlusSignedUnitNorm2576 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 i sharedSecondN02700PlusPointPosition2576‖)
          ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 sharedSecondN02700PlusSignedUpper2576
  linarith [sharedSecondN02700PlusSignedSum_norm2576, sharedSecondN02700PlusSignedCharge2576]

theorem sharedSecondN02700PlusPhysical2576 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 2 (weightedPhysical2539 (1/2) coefficients nodeModulation2541)
        sharedSecondN02700PlusPointPosition2576‖ ≤
      sharedSecondN02700PlusSignedUpper2576 := by
  have h := weightedPhysical2539_jet_le_center_error 2 (1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        sharedSecondN02700PlusPointPosition2576
  exact h.trans sharedSecondN02700PlusSignedUpper_le2576

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.sharedSecondN02700PlusSignedExpError2576
#print axioms ConnesWeilRH.Dev.sharedSecondN02700PlusSignedSum_eq2576
#print axioms ConnesWeilRH.Dev.sharedSecondN02700PlusSignedCharge2576
#print axioms ConnesWeilRH.Dev.sharedSecondN02700PlusSignedUpper_le2576
#print axioms ConnesWeilRH.Dev.sharedSecondN02700PlusPhysical2576
