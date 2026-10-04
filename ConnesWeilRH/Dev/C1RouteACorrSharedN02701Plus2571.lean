import ConnesWeilRH.Dev.C1RouteAKernelN02701Plus2555
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def corrSharedN02701PlusPosition2571 : ℝ := (((-158531586419) : ℝ) /
        51200000000)

def corrSharedN02701PlusP000Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02701PlusP000Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP000Output2571.1‖ ≤ (corrSharedN02701PlusP000Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP000BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP000Output2571,
    kernelN02701PlusP000Center2555, kernelN02701PlusP000Error2555, embedPair2542]

theorem corrSharedN02701PlusP000Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP000Output2571.1) + embedPair2542
            corrSharedN02701PlusP000Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP000Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP000Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP000Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP000Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP000Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP000Output2571, pairMagnitude2542]

def corrSharedN02701PlusP001Output2571 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP001Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP001Output2571.1‖ ≤ (corrSharedN02701PlusP001Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP001BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP001Output2571,
    kernelN02701PlusP001Center2555, kernelN02701PlusP001Error2555, embedPair2542]

theorem corrSharedN02701PlusP001Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP001Output2571.1) + embedPair2542
            corrSharedN02701PlusP001Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP001Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP001Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP001Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP001Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP001Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP001Output2571, pairMagnitude2542]

def corrSharedN02701PlusP002Output2571 : RatState2542 :=
  (((((-168036782698919993429) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-252698714645137902289) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((2260016183526325913 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP002Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP002Output2571.1‖ ≤ (corrSharedN02701PlusP002Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP002BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP002Output2571,
    kernelN02701PlusP002Center2555, kernelN02701PlusP002Error2555, embedPair2542]

theorem corrSharedN02701PlusP002Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP002Output2571.1) + embedPair2542
            corrSharedN02701PlusP002Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP002Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP002Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP002Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP002Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP002Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP002Output2571, pairMagnitude2542]

def corrSharedN02701PlusP003Output2571 : RatState2542 :=
  (((((-5788973884569169910793434755) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-4352815604563173678616329029) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((36476409710489096549727441 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP003Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP003Output2571.1‖ ≤ (corrSharedN02701PlusP003Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP003BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP003Output2571,
    kernelN02701PlusP003Center2555, kernelN02701PlusP003Error2555, embedPair2542]

theorem corrSharedN02701PlusP003Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP003Output2571.1) + embedPair2542
            corrSharedN02701PlusP003Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP003Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP003Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP003Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP003Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP003Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP003Output2571, pairMagnitude2542]

def corrSharedN02701PlusP004Output2571 : RatState2542 :=
  (((((-725790656500916187131713370187) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((4365862355930743774088204387843 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((17853934217737043702764082891 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP004Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP004Output2571.1‖ ≤ (corrSharedN02701PlusP004Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP004BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP004Output2571,
    kernelN02701PlusP004Center2555, kernelN02701PlusP004Error2555, embedPair2542]

theorem corrSharedN02701PlusP004Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP004Output2571.1) + embedPair2542
            corrSharedN02701PlusP004Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP004Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP004Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP004Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP004Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP004Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP004Output2571, pairMagnitude2542]

def corrSharedN02701PlusP005Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02701PlusP005Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP005Output2571.1‖ ≤ (corrSharedN02701PlusP005Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP005BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP005Output2571,
    kernelN02701PlusP005Center2555, kernelN02701PlusP005Error2555, embedPair2542]

theorem corrSharedN02701PlusP005Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP005Output2571.1) + embedPair2542
            corrSharedN02701PlusP005Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP005Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP005Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP005Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP005Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP005Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP005Output2571, pairMagnitude2542]

def corrSharedN02701PlusP006Output2571 : RatState2542 :=
  ((((483449294895075 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((2446198475405 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP006Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP006Output2571.1‖ ≤ (corrSharedN02701PlusP006Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP006BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP006Output2571,
    kernelN02701PlusP006Center2555, kernelN02701PlusP006Error2555, embedPair2542]

theorem corrSharedN02701PlusP006Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP006Output2571.1) + embedPair2542
            corrSharedN02701PlusP006Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP006Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP006Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP006Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP006Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP006Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP006Output2571, pairMagnitude2542]

def corrSharedN02701PlusP007Output2571 : RatState2542 :=
  ((((163354299886446954699714643 : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)),
    ((0 : ℚ) /
        1)),
    ((759335337735088749674751 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem corrSharedN02701PlusP007Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP007Output2571.1‖ ≤ (corrSharedN02701PlusP007Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP007BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP007Output2571,
    kernelN02701PlusP007Center2555, kernelN02701PlusP007Error2555, embedPair2542]

theorem corrSharedN02701PlusP007Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP007Output2571.1) + embedPair2542
            corrSharedN02701PlusP007Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP007Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP007Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP007Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP007Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP007Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP007Output2571, pairMagnitude2542]

def corrSharedN02701PlusP008Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP008Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP008Output2571.1‖ ≤ (corrSharedN02701PlusP008Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP008BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP008Output2571,
    kernelN02701PlusP008Center2555, kernelN02701PlusP008Error2555, embedPair2542]

theorem corrSharedN02701PlusP008Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP008Output2571.1) + embedPair2542
            corrSharedN02701PlusP008Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP008Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP008Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP008Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP008Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP008Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP008Output2571, pairMagnitude2542]

def corrSharedN02701PlusP009Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP009Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP009Output2571.1‖ ≤ (corrSharedN02701PlusP009Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP009BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP009Output2571,
    kernelN02701PlusP009Center2555, kernelN02701PlusP009Error2555, embedPair2542]

theorem corrSharedN02701PlusP009Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP009Output2571.1) + embedPair2542
            corrSharedN02701PlusP009Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP009Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP009Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP009Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP009Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP009Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP009Output2571, pairMagnitude2542]

def corrSharedN02701PlusP010Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP010Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP010Output2571.1‖ ≤ (corrSharedN02701PlusP010Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP010BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP010Output2571,
    kernelN02701PlusP010Center2555, kernelN02701PlusP010Error2555, embedPair2542]

theorem corrSharedN02701PlusP010Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP010Output2571.1) + embedPair2542
            corrSharedN02701PlusP010Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP010Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP010Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP010Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP010Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP010Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP010Output2571, pairMagnitude2542]

def corrSharedN02701PlusP011Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP011Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP011Output2571.1‖ ≤ (corrSharedN02701PlusP011Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP011BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP011Output2571,
    kernelN02701PlusP011Center2555, kernelN02701PlusP011Error2555, embedPair2542]

theorem corrSharedN02701PlusP011Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP011Output2571.1) + embedPair2542
            corrSharedN02701PlusP011Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP011Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP011Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP011Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP011Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP011Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP011Output2571, pairMagnitude2542]

def corrSharedN02701PlusP012Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP012Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP012Output2571.1‖ ≤ (corrSharedN02701PlusP012Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP012BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP012Output2571,
    kernelN02701PlusP012Center2555, kernelN02701PlusP012Error2555, embedPair2542]

theorem corrSharedN02701PlusP012Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP012Output2571.1) + embedPair2542
            corrSharedN02701PlusP012Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP012Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP012Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP012Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP012Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP012Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP012Output2571, pairMagnitude2542]

def corrSharedN02701PlusP013Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP013Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP013Output2571.1‖ ≤ (corrSharedN02701PlusP013Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP013BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP013Output2571,
    kernelN02701PlusP013Center2555, kernelN02701PlusP013Error2555, embedPair2542]

theorem corrSharedN02701PlusP013Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP013Output2571.1) + embedPair2542
            corrSharedN02701PlusP013Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP013Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP013Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP013Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP013Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP013Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP013Output2571, pairMagnitude2542]

def corrSharedN02701PlusP014Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP014Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP014Output2571.1‖ ≤ (corrSharedN02701PlusP014Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP014BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP014Output2571,
    kernelN02701PlusP014Center2555, kernelN02701PlusP014Error2555, embedPair2542]

theorem corrSharedN02701PlusP014Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP014Output2571.1) + embedPair2542
            corrSharedN02701PlusP014Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP014Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP014Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP014Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP014Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP014Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP014Output2571, pairMagnitude2542]

def corrSharedN02701PlusP015Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP015Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP015Output2571.1‖ ≤ (corrSharedN02701PlusP015Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP015BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP015Output2571,
    kernelN02701PlusP015Center2555, kernelN02701PlusP015Error2555, embedPair2542]

theorem corrSharedN02701PlusP015Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP015Output2571.1) + embedPair2542
            corrSharedN02701PlusP015Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP015Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP015Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP015Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP015Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP015Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP015Output2571, pairMagnitude2542]

def corrSharedN02701PlusP016Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP016Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP016Output2571.1‖ ≤ (corrSharedN02701PlusP016Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP016BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP016Output2571,
    kernelN02701PlusP016Center2555, kernelN02701PlusP016Error2555, embedPair2542]

theorem corrSharedN02701PlusP016Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP016Output2571.1) + embedPair2542
            corrSharedN02701PlusP016Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP016Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP016Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP016Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP016Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP016Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP016Output2571, pairMagnitude2542]

def corrSharedN02701PlusP017Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP017Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP017Output2571.1‖ ≤ (corrSharedN02701PlusP017Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP017BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP017Output2571,
    kernelN02701PlusP017Center2555, kernelN02701PlusP017Error2555, embedPair2542]

theorem corrSharedN02701PlusP017Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP017Output2571.1) + embedPair2542
            corrSharedN02701PlusP017Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP017Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP017Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP017Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP017Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP017Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP017Output2571, pairMagnitude2542]

def corrSharedN02701PlusP018Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP018Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP018Output2571.1‖ ≤ (corrSharedN02701PlusP018Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP018BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP018Output2571,
    kernelN02701PlusP018Center2555, kernelN02701PlusP018Error2555, embedPair2542]

theorem corrSharedN02701PlusP018Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP018Output2571.1) + embedPair2542
            corrSharedN02701PlusP018Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP018Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP018Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP018Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP018Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP018Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP018Output2571, pairMagnitude2542]

def corrSharedN02701PlusP019Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP019Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP019Output2571.1‖ ≤ (corrSharedN02701PlusP019Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP019BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP019Output2571,
    kernelN02701PlusP019Center2555, kernelN02701PlusP019Error2555, embedPair2542]

theorem corrSharedN02701PlusP019Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP019Output2571.1) + embedPair2542
            corrSharedN02701PlusP019Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP019Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP019Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP019Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP019Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP019Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP019Output2571, pairMagnitude2542]

def corrSharedN02701PlusP020Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP020Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP020Output2571.1‖ ≤ (corrSharedN02701PlusP020Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP020BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP020Output2571,
    kernelN02701PlusP020Center2555, kernelN02701PlusP020Error2555, embedPair2542]

theorem corrSharedN02701PlusP020Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP020Output2571.1) + embedPair2542
            corrSharedN02701PlusP020Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP020Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP020Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP020Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP020Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP020Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP020Output2571, pairMagnitude2542]

def corrSharedN02701PlusP021Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP021Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP021Output2571.1‖ ≤ (corrSharedN02701PlusP021Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP021BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP021Output2571,
    kernelN02701PlusP021Center2555, kernelN02701PlusP021Error2555, embedPair2542]

theorem corrSharedN02701PlusP021Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP021Output2571.1) + embedPair2542
            corrSharedN02701PlusP021Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP021Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP021Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP021Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP021Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP021Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP021Output2571, pairMagnitude2542]

def corrSharedN02701PlusP022Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP022Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP022Output2571.1‖ ≤ (corrSharedN02701PlusP022Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP022BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP022Output2571,
    kernelN02701PlusP022Center2555, kernelN02701PlusP022Error2555, embedPair2542]

theorem corrSharedN02701PlusP022Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP022Output2571.1) + embedPair2542
            corrSharedN02701PlusP022Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP022Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP022Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP022Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP022Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP022Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP022Output2571, pairMagnitude2542]

def corrSharedN02701PlusP023Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP023Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP023Output2571.1‖ ≤ (corrSharedN02701PlusP023Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP023BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP023Output2571,
    kernelN02701PlusP023Center2555, kernelN02701PlusP023Error2555, embedPair2542]

theorem corrSharedN02701PlusP023Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP023Output2571.1) + embedPair2542
            corrSharedN02701PlusP023Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP023Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP023Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP023Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP023Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP023Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP023Output2571, pairMagnitude2542]

def corrSharedN02701PlusP024Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP024Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP024Output2571.1‖ ≤ (corrSharedN02701PlusP024Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP024BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP024Output2571,
    kernelN02701PlusP024Center2555, kernelN02701PlusP024Error2555, embedPair2542]

theorem corrSharedN02701PlusP024Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP024Output2571.1) + embedPair2542
            corrSharedN02701PlusP024Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP024Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP024Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP024Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP024Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP024Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP024Output2571, pairMagnitude2542]

def corrSharedN02701PlusP025Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP025Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP025Output2571.1‖ ≤ (corrSharedN02701PlusP025Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP025BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP025Output2571,
    kernelN02701PlusP025Center2555, kernelN02701PlusP025Error2555, embedPair2542]

theorem corrSharedN02701PlusP025Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP025Output2571.1) + embedPair2542
            corrSharedN02701PlusP025Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP025Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP025Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP025Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP025Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP025Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP025Output2571, pairMagnitude2542]

def corrSharedN02701PlusP026Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP026Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP026Output2571.1‖ ≤ (corrSharedN02701PlusP026Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP026BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP026Output2571,
    kernelN02701PlusP026Center2555, kernelN02701PlusP026Error2555, embedPair2542]

theorem corrSharedN02701PlusP026Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP026Output2571.1) + embedPair2542
            corrSharedN02701PlusP026Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP026Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP026Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP026Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP026Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP026Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP026Output2571, pairMagnitude2542]

def corrSharedN02701PlusP027Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP027Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP027Output2571.1‖ ≤ (corrSharedN02701PlusP027Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP027BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP027Output2571,
    kernelN02701PlusP027Center2555, kernelN02701PlusP027Error2555, embedPair2542]

theorem corrSharedN02701PlusP027Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP027Output2571.1) + embedPair2542
            corrSharedN02701PlusP027Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP027Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP027Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP027Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP027Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP027Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP027Output2571, pairMagnitude2542]

def corrSharedN02701PlusP028Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP028Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP028Output2571.1‖ ≤ (corrSharedN02701PlusP028Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP028BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP028Output2571,
    kernelN02701PlusP028Center2555, kernelN02701PlusP028Error2555, embedPair2542]

theorem corrSharedN02701PlusP028Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP028Output2571.1) + embedPair2542
            corrSharedN02701PlusP028Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP028Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP028Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP028Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP028Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP028Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP028Output2571, pairMagnitude2542]

def corrSharedN02701PlusP029Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701PlusP029Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP029Output2571.1‖ ≤ (corrSharedN02701PlusP029Output2571.2 : ℝ) :=
                by
  have h := kernelN02701PlusP029BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701PlusPosition2571, kernelN02701PlusPosition2555,
      corrSharedN02701PlusP029Output2571,
    kernelN02701PlusP029Center2555, kernelN02701PlusP029Error2555, embedPair2542]

theorem corrSharedN02701PlusP029Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02701PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP029Output2571.1) + embedPair2542
            corrSharedN02701PlusP029Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02701PlusPosition2571 - embedPair2542
            corrSharedN02701PlusP029Output2571.1‖ + ‖embedPair2542
            corrSharedN02701PlusP029Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701PlusP029Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701PlusP029Output2571.1 : ℝ) :=
      add_le_add corrSharedN02701PlusP029Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701PlusP029Output2571, pairMagnitude2542]

noncomputable def corrSharedN02701PlusValue2571 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 corrSharedN02701PlusP000Output2571.1
  | 1 => embedPair2542 corrSharedN02701PlusP001Output2571.1
  | 2 => embedPair2542 corrSharedN02701PlusP002Output2571.1
  | 3 => embedPair2542 corrSharedN02701PlusP003Output2571.1
  | 4 => embedPair2542 corrSharedN02701PlusP004Output2571.1
  | 5 => embedPair2542 corrSharedN02701PlusP005Output2571.1
  | 6 => embedPair2542 corrSharedN02701PlusP006Output2571.1
  | 7 => embedPair2542 corrSharedN02701PlusP007Output2571.1
  | 8 => embedPair2542 corrSharedN02701PlusP008Output2571.1
  | 9 => embedPair2542 corrSharedN02701PlusP009Output2571.1
  | 10 => embedPair2542 corrSharedN02701PlusP010Output2571.1
  | 11 => embedPair2542 corrSharedN02701PlusP011Output2571.1
  | 12 => embedPair2542 corrSharedN02701PlusP012Output2571.1
  | 13 => embedPair2542 corrSharedN02701PlusP013Output2571.1
  | 14 => embedPair2542 corrSharedN02701PlusP014Output2571.1
  | 15 => embedPair2542 corrSharedN02701PlusP015Output2571.1
  | 16 => embedPair2542 corrSharedN02701PlusP016Output2571.1
  | 17 => embedPair2542 corrSharedN02701PlusP017Output2571.1
  | 18 => embedPair2542 corrSharedN02701PlusP018Output2571.1
  | 19 => embedPair2542 corrSharedN02701PlusP019Output2571.1
  | 20 => embedPair2542 corrSharedN02701PlusP020Output2571.1
  | 21 => embedPair2542 corrSharedN02701PlusP021Output2571.1
  | 22 => embedPair2542 corrSharedN02701PlusP022Output2571.1
  | 23 => embedPair2542 corrSharedN02701PlusP023Output2571.1
  | 24 => embedPair2542 corrSharedN02701PlusP024Output2571.1
  | 25 => embedPair2542 corrSharedN02701PlusP025Output2571.1
  | 26 => embedPair2542 corrSharedN02701PlusP026Output2571.1
  | 27 => embedPair2542 corrSharedN02701PlusP027Output2571.1
  | 28 => embedPair2542 corrSharedN02701PlusP028Output2571.1
  | 29 => embedPair2542 corrSharedN02701PlusP029Output2571.1
  | _ => 0

noncomputable def corrSharedN02701PlusError2571 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (corrSharedN02701PlusP000Output2571.2 : ℝ)
  | 1 => (corrSharedN02701PlusP001Output2571.2 : ℝ)
  | 2 => (corrSharedN02701PlusP002Output2571.2 : ℝ)
  | 3 => (corrSharedN02701PlusP003Output2571.2 : ℝ)
  | 4 => (corrSharedN02701PlusP004Output2571.2 : ℝ)
  | 5 => (corrSharedN02701PlusP005Output2571.2 : ℝ)
  | 6 => (corrSharedN02701PlusP006Output2571.2 : ℝ)
  | 7 => (corrSharedN02701PlusP007Output2571.2 : ℝ)
  | 8 => (corrSharedN02701PlusP008Output2571.2 : ℝ)
  | 9 => (corrSharedN02701PlusP009Output2571.2 : ℝ)
  | 10 => (corrSharedN02701PlusP010Output2571.2 : ℝ)
  | 11 => (corrSharedN02701PlusP011Output2571.2 : ℝ)
  | 12 => (corrSharedN02701PlusP012Output2571.2 : ℝ)
  | 13 => (corrSharedN02701PlusP013Output2571.2 : ℝ)
  | 14 => (corrSharedN02701PlusP014Output2571.2 : ℝ)
  | 15 => (corrSharedN02701PlusP015Output2571.2 : ℝ)
  | 16 => (corrSharedN02701PlusP016Output2571.2 : ℝ)
  | 17 => (corrSharedN02701PlusP017Output2571.2 : ℝ)
  | 18 => (corrSharedN02701PlusP018Output2571.2 : ℝ)
  | 19 => (corrSharedN02701PlusP019Output2571.2 : ℝ)
  | 20 => (corrSharedN02701PlusP020Output2571.2 : ℝ)
  | 21 => (corrSharedN02701PlusP021Output2571.2 : ℝ)
  | 22 => (corrSharedN02701PlusP022Output2571.2 : ℝ)
  | 23 => (corrSharedN02701PlusP023Output2571.2 : ℝ)
  | 24 => (corrSharedN02701PlusP024Output2571.2 : ℝ)
  | 25 => (corrSharedN02701PlusP025Output2571.2 : ℝ)
  | 26 => (corrSharedN02701PlusP026Output2571.2 : ℝ)
  | 27 => (corrSharedN02701PlusP027Output2571.2 : ℝ)
  | 28 => (corrSharedN02701PlusP028Output2571.2 : ℝ)
  | 29 => (corrSharedN02701PlusP029Output2571.2 : ℝ)
  | _ => 0

theorem corrSharedN02701PlusExp_error2571 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i corrSharedN02701PlusPosition2571 - corrSharedN02701PlusValue2571
            i‖ ≤
            corrSharedN02701PlusError2571 i := by
  fin_cases i
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP000Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP001Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP002Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP003Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP004Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP005Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP006Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP007Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP008Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP009Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP010Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP011Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP012Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP013Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP014Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP015Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP016Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP017Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP018Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP019Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP020Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP021Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP022Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP023Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP024Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP025Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP026Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP027Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP028Error2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP029Error2571

theorem corrSharedN02701PlusUnit_norm2571 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i corrSharedN02701PlusPosition2571‖ ≤ 1 := by
  fin_cases i
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP000Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP001Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP002Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP003Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP004Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP005Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP006Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP007Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP008Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP009Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP010Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP011Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP012Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP013Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP014Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP015Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP016Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP017Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP018Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP019Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP020Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP021Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP022Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP023Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP024Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP025Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP026Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP027Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP028Norm2571
  · simpa only [corrSharedN02701PlusValue2571, corrSharedN02701PlusError2571] using
      corrSharedN02701PlusP029Norm2571

noncomputable def corrSharedN02701PlusSumValue2571 : ℂ := ⟨(((((867202040066610422419128848 *
    10^40
        + 6785745650493705456991215711021751867201) * 10^40
        + 9054917372334823418446382245404970199156) * 10^40
        + 566919448777187724118175832569398108031) : ℝ) /
        (((1636695303948070935006594848413 * 10^40
        + 7995761083210230215323947416456840480668) * 10^40
        + 9820233727744163504616295207857544334206) * 10^40
        + 3780035504608628272942696526664263794688)),
    (((-(((186451851566905808823017362 * 10^40
        + 7540587836771375372856150615428490748569) * 10^40
        + 7007438982234954107613626526276101912) * 10^40
        + 4576263505500115064896652066218967860431)) : ℝ) /
        (((409173825987017733751648712103 * 10^40
        + 4498940270802557553830986854114210120167) * 10^40
        + 2455058431936040876154073801964386083551) * 10^40
        + 5945008876152157068235674131666065948672))⟩

noncomputable def corrSharedN02701PlusUpper2571 : ℝ := ((3494223 : ℝ) /
        5000000000)

theorem corrSharedN02701PlusSum_eq2571 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02701PlusValue2571 i) =
      corrSharedN02701PlusSumValue2571 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        corrSharedN02701PlusValue2571,
      corrSharedN02701PlusSumValue2571, embedPair2542, corrSharedN02701PlusP000Output2571,
      corrSharedN02701PlusP001Output2571,
      corrSharedN02701PlusP002Output2571,
      corrSharedN02701PlusP003Output2571,
      corrSharedN02701PlusP004Output2571,
      corrSharedN02701PlusP005Output2571,
      corrSharedN02701PlusP006Output2571,
      corrSharedN02701PlusP007Output2571,
      corrSharedN02701PlusP008Output2571,
      corrSharedN02701PlusP009Output2571,
      corrSharedN02701PlusP010Output2571,
      corrSharedN02701PlusP011Output2571,
      corrSharedN02701PlusP012Output2571,
      corrSharedN02701PlusP013Output2571,
      corrSharedN02701PlusP014Output2571,
      corrSharedN02701PlusP015Output2571,
      corrSharedN02701PlusP016Output2571,
      corrSharedN02701PlusP017Output2571,
      corrSharedN02701PlusP018Output2571,
      corrSharedN02701PlusP019Output2571,
      corrSharedN02701PlusP020Output2571,
      corrSharedN02701PlusP021Output2571,
      corrSharedN02701PlusP022Output2571,
      corrSharedN02701PlusP023Output2571,
      corrSharedN02701PlusP024Output2571,
      corrSharedN02701PlusP025Output2571,
      corrSharedN02701PlusP026Output2571,
      corrSharedN02701PlusP027Output2571,
      corrSharedN02701PlusP028Output2571,
      corrSharedN02701PlusP029Output2571, Complex.mul_re, Complex.mul_im]

theorem corrSharedN02701PlusSum_norm2571 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02701PlusValue2571 i‖ ≤
      ((1397689 : ℝ) /
        2000000000) := by
  rw [corrSharedN02701PlusSum_eq2571]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [corrSharedN02701PlusSumValue2571]

theorem corrSharedN02701PlusEvaluation_charge2571 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * corrSharedN02701PlusError2571 i) ≤ (1 : ℝ)/10^12
          := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      corrSharedN02701PlusError2571,
      corrSharedN02701PlusP000Output2571,
      corrSharedN02701PlusP001Output2571,
      corrSharedN02701PlusP002Output2571,
      corrSharedN02701PlusP003Output2571,
      corrSharedN02701PlusP004Output2571,
      corrSharedN02701PlusP005Output2571,
      corrSharedN02701PlusP006Output2571,
      corrSharedN02701PlusP007Output2571,
      corrSharedN02701PlusP008Output2571,
      corrSharedN02701PlusP009Output2571,
      corrSharedN02701PlusP010Output2571,
      corrSharedN02701PlusP011Output2571,
      corrSharedN02701PlusP012Output2571,
      corrSharedN02701PlusP013Output2571,
      corrSharedN02701PlusP014Output2571,
      corrSharedN02701PlusP015Output2571,
      corrSharedN02701PlusP016Output2571,
      corrSharedN02701PlusP017Output2571,
      corrSharedN02701PlusP018Output2571,
      corrSharedN02701PlusP019Output2571,
      corrSharedN02701PlusP020Output2571,
      corrSharedN02701PlusP021Output2571,
      corrSharedN02701PlusP022Output2571,
      corrSharedN02701PlusP023Output2571,
      corrSharedN02701PlusP024Output2571,
      corrSharedN02701PlusP025Output2571,
      corrSharedN02701PlusP026Output2571,
      corrSharedN02701PlusP027Output2571,
      corrSharedN02701PlusP028Output2571,
      corrSharedN02701PlusP029Output2571]

theorem corrSharedN02701PlusSigned_le2571 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 corrSharedN02701PlusPosition2571 ≤ corrSharedN02701PlusUpper2571 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i corrSharedN02701PlusPosition2571‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02701PlusValue2571 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * corrSharedN02701PlusError2571 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (corrSharedN02701PlusExp_error2571 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i corrSharedN02701PlusPosition2571‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (corrSharedN02701PlusUnit_norm2571 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i corrSharedN02701PlusPosition2571‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 corrSharedN02701PlusUpper2571
  linarith [corrSharedN02701PlusSum_norm2571, corrSharedN02701PlusEvaluation_charge2571]

theorem corrSharedN02701PlusPhysical_le2571 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 corrSharedN02701PlusPosition2571‖ ≤
      corrSharedN02701PlusUpper2571 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        corrSharedN02701PlusPosition2571
  simpa only [iteratedDeriv_zero] using h.trans corrSharedN02701PlusSigned_le2571

theorem corrSharedN02701PlusGrid2571 :
    -stripRadius2303 + (2701 : ℝ)*(2*stripRadius2303/10240) = corrSharedN02701PlusPosition2571 :=
        by
  norm_num [stripRadius2303, corrSharedN02701PlusPosition2571]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrSharedN02701PlusSigned_le2571
#print axioms ConnesWeilRH.Dev.corrSharedN02701PlusPhysical_le2571
