import ConnesWeilRH.Dev.C1RouteAKernelN02700Plus2555
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def corrSharedN02700PlusPosition2571 : ℝ := (((-7929856121) : ℝ) /
        2560000000)

def corrSharedN02700PlusP000Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP000Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP000Output2571.1‖ ≤ (corrSharedN02700PlusP000Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP000BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP000Output2571,
    kernelN02700PlusP000Center2555, kernelN02700PlusP000Error2555, embedPair2542]

theorem corrSharedN02700PlusP000Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP000Output2571.1) + embedPair2542
            corrSharedN02700PlusP000Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP000Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP000Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP000Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP000Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP000Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP000Output2571, pairMagnitude2542]

def corrSharedN02700PlusP001Output2571 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02700PlusP001Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP001Output2571.1‖ ≤ (corrSharedN02700PlusP001Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP001BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP001Output2571,
    kernelN02700PlusP001Center2555, kernelN02700PlusP001Error2555, embedPair2542]

theorem corrSharedN02700PlusP001Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP001Output2571.1) + embedPair2542
            corrSharedN02700PlusP001Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP001Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP001Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP001Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP001Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP001Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP001Output2571, pairMagnitude2542]

def corrSharedN02700PlusP002Output2571 : RatState2542 :=
  (((((-342022637592315929245) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-462193622279321905361) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((2124679950171895707 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02700PlusP002Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP002Output2571.1‖ ≤ (corrSharedN02700PlusP002Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP002BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP002Output2571,
    kernelN02700PlusP002Center2555, kernelN02700PlusP002Error2555, embedPair2542]

theorem corrSharedN02700PlusP002Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP002Output2571.1) + embedPair2542
            corrSharedN02700PlusP002Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP002Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP002Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP002Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP002Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP002Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP002Output2571, pairMagnitude2542]

def corrSharedN02700PlusP003Output2571 : RatState2542 :=
  (((((-3050957105819623379802289723) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-4122922757640557388486708103) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((35512274632534440194531833 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02700PlusP003Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP003Output2571.1‖ ≤ (corrSharedN02700PlusP003Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP003BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP003Output2571,
    kernelN02700PlusP003Center2555, kernelN02700PlusP003Error2555, embedPair2542]

theorem corrSharedN02700PlusP003Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP003Output2571.1) + embedPair2542
            corrSharedN02700PlusP003Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP003Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP003Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP003Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP003Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP003Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP003Output2571, pairMagnitude2542]

def corrSharedN02700PlusP004Output2571 : RatState2542 :=
  (((((-3088285000154142764160101575539) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((4173365952909685099392742956493 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((4385370515285168518352942979 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem corrSharedN02700PlusP004Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP004Output2571.1‖ ≤ (corrSharedN02700PlusP004Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP004BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP004Output2571,
    kernelN02700PlusP004Center2555, kernelN02700PlusP004Error2555, embedPair2542]

theorem corrSharedN02700PlusP004Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP004Output2571.1) + embedPair2542
            corrSharedN02700PlusP004Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP004Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP004Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP004Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP004Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP004Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP004Output2571, pairMagnitude2542]

def corrSharedN02700PlusP005Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP005Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP005Output2571.1‖ ≤ (corrSharedN02700PlusP005Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP005BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP005Output2571,
    kernelN02700PlusP005Center2555, kernelN02700PlusP005Error2555, embedPair2542]

theorem corrSharedN02700PlusP005Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP005Output2571.1) + embedPair2542
            corrSharedN02700PlusP005Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP005Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP005Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP005Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP005Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP005Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP005Output2571, pairMagnitude2542]

def corrSharedN02700PlusP006Output2571 : RatState2542 :=
  ((((440386906605911 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((2424345947741 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02700PlusP006Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP006Output2571.1‖ ≤ (corrSharedN02700PlusP006Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP006BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP006Output2571,
    kernelN02700PlusP006Center2555, kernelN02700PlusP006Error2555, embedPair2542]

theorem corrSharedN02700PlusP006Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP006Output2571.1) + embedPair2542
            corrSharedN02700PlusP006Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP006Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP006Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP006Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP006Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP006Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP006Output2571, pairMagnitude2542]

def corrSharedN02700PlusP007Output2571 : RatState2542 :=
  ((((1282254638493795595923663161 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1)),
    ((372637180338657148206451 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem corrSharedN02700PlusP007Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP007Output2571.1‖ ≤ (corrSharedN02700PlusP007Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP007BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP007Output2571,
    kernelN02700PlusP007Center2555, kernelN02700PlusP007Error2555, embedPair2542]

theorem corrSharedN02700PlusP007Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP007Output2571.1) + embedPair2542
            corrSharedN02700PlusP007Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP007Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP007Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP007Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP007Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP007Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP007Output2571, pairMagnitude2542]

def corrSharedN02700PlusP008Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP008Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP008Output2571.1‖ ≤ (corrSharedN02700PlusP008Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP008BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP008Output2571,
    kernelN02700PlusP008Center2555, kernelN02700PlusP008Error2555, embedPair2542]

theorem corrSharedN02700PlusP008Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP008Output2571.1) + embedPair2542
            corrSharedN02700PlusP008Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP008Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP008Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP008Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP008Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP008Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP008Output2571, pairMagnitude2542]

def corrSharedN02700PlusP009Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP009Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP009Output2571.1‖ ≤ (corrSharedN02700PlusP009Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP009BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP009Output2571,
    kernelN02700PlusP009Center2555, kernelN02700PlusP009Error2555, embedPair2542]

theorem corrSharedN02700PlusP009Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP009Output2571.1) + embedPair2542
            corrSharedN02700PlusP009Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP009Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP009Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP009Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP009Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP009Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP009Output2571, pairMagnitude2542]

def corrSharedN02700PlusP010Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP010Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP010Output2571.1‖ ≤ (corrSharedN02700PlusP010Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP010BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP010Output2571,
    kernelN02700PlusP010Center2555, kernelN02700PlusP010Error2555, embedPair2542]

theorem corrSharedN02700PlusP010Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP010Output2571.1) + embedPair2542
            corrSharedN02700PlusP010Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP010Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP010Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP010Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP010Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP010Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP010Output2571, pairMagnitude2542]

def corrSharedN02700PlusP011Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP011Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP011Output2571.1‖ ≤ (corrSharedN02700PlusP011Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP011BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP011Output2571,
    kernelN02700PlusP011Center2555, kernelN02700PlusP011Error2555, embedPair2542]

theorem corrSharedN02700PlusP011Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP011Output2571.1) + embedPair2542
            corrSharedN02700PlusP011Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP011Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP011Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP011Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP011Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP011Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP011Output2571, pairMagnitude2542]

def corrSharedN02700PlusP012Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP012Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP012Output2571.1‖ ≤ (corrSharedN02700PlusP012Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP012BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP012Output2571,
    kernelN02700PlusP012Center2555, kernelN02700PlusP012Error2555, embedPair2542]

theorem corrSharedN02700PlusP012Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP012Output2571.1) + embedPair2542
            corrSharedN02700PlusP012Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP012Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP012Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP012Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP012Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP012Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP012Output2571, pairMagnitude2542]

def corrSharedN02700PlusP013Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP013Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP013Output2571.1‖ ≤ (corrSharedN02700PlusP013Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP013BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP013Output2571,
    kernelN02700PlusP013Center2555, kernelN02700PlusP013Error2555, embedPair2542]

theorem corrSharedN02700PlusP013Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP013Output2571.1) + embedPair2542
            corrSharedN02700PlusP013Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP013Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP013Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP013Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP013Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP013Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP013Output2571, pairMagnitude2542]

def corrSharedN02700PlusP014Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP014Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP014Output2571.1‖ ≤ (corrSharedN02700PlusP014Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP014BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP014Output2571,
    kernelN02700PlusP014Center2555, kernelN02700PlusP014Error2555, embedPair2542]

theorem corrSharedN02700PlusP014Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP014Output2571.1) + embedPair2542
            corrSharedN02700PlusP014Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP014Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP014Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP014Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP014Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP014Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP014Output2571, pairMagnitude2542]

def corrSharedN02700PlusP015Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP015Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP015Output2571.1‖ ≤ (corrSharedN02700PlusP015Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP015BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP015Output2571,
    kernelN02700PlusP015Center2555, kernelN02700PlusP015Error2555, embedPair2542]

theorem corrSharedN02700PlusP015Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP015Output2571.1) + embedPair2542
            corrSharedN02700PlusP015Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP015Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP015Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP015Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP015Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP015Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP015Output2571, pairMagnitude2542]

def corrSharedN02700PlusP016Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP016Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP016Output2571.1‖ ≤ (corrSharedN02700PlusP016Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP016BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP016Output2571,
    kernelN02700PlusP016Center2555, kernelN02700PlusP016Error2555, embedPair2542]

theorem corrSharedN02700PlusP016Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP016Output2571.1) + embedPair2542
            corrSharedN02700PlusP016Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP016Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP016Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP016Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP016Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP016Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP016Output2571, pairMagnitude2542]

def corrSharedN02700PlusP017Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP017Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP017Output2571.1‖ ≤ (corrSharedN02700PlusP017Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP017BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP017Output2571,
    kernelN02700PlusP017Center2555, kernelN02700PlusP017Error2555, embedPair2542]

theorem corrSharedN02700PlusP017Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP017Output2571.1) + embedPair2542
            corrSharedN02700PlusP017Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP017Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP017Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP017Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP017Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP017Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP017Output2571, pairMagnitude2542]

def corrSharedN02700PlusP018Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP018Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP018Output2571.1‖ ≤ (corrSharedN02700PlusP018Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP018BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP018Output2571,
    kernelN02700PlusP018Center2555, kernelN02700PlusP018Error2555, embedPair2542]

theorem corrSharedN02700PlusP018Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP018Output2571.1) + embedPair2542
            corrSharedN02700PlusP018Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP018Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP018Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP018Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP018Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP018Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP018Output2571, pairMagnitude2542]

def corrSharedN02700PlusP019Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP019Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP019Output2571.1‖ ≤ (corrSharedN02700PlusP019Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP019BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP019Output2571,
    kernelN02700PlusP019Center2555, kernelN02700PlusP019Error2555, embedPair2542]

theorem corrSharedN02700PlusP019Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP019Output2571.1) + embedPair2542
            corrSharedN02700PlusP019Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP019Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP019Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP019Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP019Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP019Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP019Output2571, pairMagnitude2542]

def corrSharedN02700PlusP020Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP020Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP020Output2571.1‖ ≤ (corrSharedN02700PlusP020Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP020BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP020Output2571,
    kernelN02700PlusP020Center2555, kernelN02700PlusP020Error2555, embedPair2542]

theorem corrSharedN02700PlusP020Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP020Output2571.1) + embedPair2542
            corrSharedN02700PlusP020Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP020Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP020Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP020Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP020Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP020Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP020Output2571, pairMagnitude2542]

def corrSharedN02700PlusP021Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP021Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP021Output2571.1‖ ≤ (corrSharedN02700PlusP021Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP021BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP021Output2571,
    kernelN02700PlusP021Center2555, kernelN02700PlusP021Error2555, embedPair2542]

theorem corrSharedN02700PlusP021Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP021Output2571.1) + embedPair2542
            corrSharedN02700PlusP021Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP021Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP021Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP021Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP021Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP021Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP021Output2571, pairMagnitude2542]

def corrSharedN02700PlusP022Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP022Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP022Output2571.1‖ ≤ (corrSharedN02700PlusP022Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP022BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP022Output2571,
    kernelN02700PlusP022Center2555, kernelN02700PlusP022Error2555, embedPair2542]

theorem corrSharedN02700PlusP022Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP022Output2571.1) + embedPair2542
            corrSharedN02700PlusP022Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP022Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP022Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP022Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP022Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP022Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP022Output2571, pairMagnitude2542]

def corrSharedN02700PlusP023Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP023Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP023Output2571.1‖ ≤ (corrSharedN02700PlusP023Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP023BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP023Output2571,
    kernelN02700PlusP023Center2555, kernelN02700PlusP023Error2555, embedPair2542]

theorem corrSharedN02700PlusP023Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP023Output2571.1) + embedPair2542
            corrSharedN02700PlusP023Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP023Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP023Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP023Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP023Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP023Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP023Output2571, pairMagnitude2542]

def corrSharedN02700PlusP024Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP024Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP024Output2571.1‖ ≤ (corrSharedN02700PlusP024Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP024BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP024Output2571,
    kernelN02700PlusP024Center2555, kernelN02700PlusP024Error2555, embedPair2542]

theorem corrSharedN02700PlusP024Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP024Output2571.1) + embedPair2542
            corrSharedN02700PlusP024Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP024Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP024Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP024Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP024Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP024Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP024Output2571, pairMagnitude2542]

def corrSharedN02700PlusP025Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP025Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP025Output2571.1‖ ≤ (corrSharedN02700PlusP025Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP025BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP025Output2571,
    kernelN02700PlusP025Center2555, kernelN02700PlusP025Error2555, embedPair2542]

theorem corrSharedN02700PlusP025Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP025Output2571.1) + embedPair2542
            corrSharedN02700PlusP025Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP025Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP025Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP025Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP025Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP025Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP025Output2571, pairMagnitude2542]

def corrSharedN02700PlusP026Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP026Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP026Output2571.1‖ ≤ (corrSharedN02700PlusP026Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP026BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP026Output2571,
    kernelN02700PlusP026Center2555, kernelN02700PlusP026Error2555, embedPair2542]

theorem corrSharedN02700PlusP026Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP026Output2571.1) + embedPair2542
            corrSharedN02700PlusP026Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP026Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP026Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP026Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP026Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP026Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP026Output2571, pairMagnitude2542]

def corrSharedN02700PlusP027Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP027Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP027Output2571.1‖ ≤ (corrSharedN02700PlusP027Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP027BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP027Output2571,
    kernelN02700PlusP027Center2555, kernelN02700PlusP027Error2555, embedPair2542]

theorem corrSharedN02700PlusP027Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP027Output2571.1) + embedPair2542
            corrSharedN02700PlusP027Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP027Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP027Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP027Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP027Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP027Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP027Output2571, pairMagnitude2542]

def corrSharedN02700PlusP028Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP028Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP028Output2571.1‖ ≤ (corrSharedN02700PlusP028Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP028BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP028Output2571,
    kernelN02700PlusP028Center2555, kernelN02700PlusP028Error2555, embedPair2542]

theorem corrSharedN02700PlusP028Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP028Output2571.1) + embedPair2542
            corrSharedN02700PlusP028Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP028Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP028Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP028Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP028Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP028Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP028Output2571, pairMagnitude2542]

def corrSharedN02700PlusP029Output2571 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700PlusP029Error2571 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP029Output2571.1‖ ≤ (corrSharedN02700PlusP029Output2571.2 : ℝ) :=
                by
  have h := kernelN02700PlusP029BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700PlusPosition2571, kernelN02700PlusPosition2555,
      corrSharedN02700PlusP029Output2571,
    kernelN02700PlusP029Center2555, kernelN02700PlusP029Error2555, embedPair2542]

theorem corrSharedN02700PlusP029Norm2571 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02700PlusPosition2571‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP029Output2571.1) + embedPair2542
            corrSharedN02700PlusP029Output2571.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02700PlusPosition2571 - embedPair2542
            corrSharedN02700PlusP029Output2571.1‖ + ‖embedPair2542
            corrSharedN02700PlusP029Output2571.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700PlusP029Output2571.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700PlusP029Output2571.1 : ℝ) :=
      add_le_add corrSharedN02700PlusP029Error2571 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700PlusP029Output2571, pairMagnitude2542]

noncomputable def corrSharedN02700PlusValue2571 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 corrSharedN02700PlusP000Output2571.1
  | 1 => embedPair2542 corrSharedN02700PlusP001Output2571.1
  | 2 => embedPair2542 corrSharedN02700PlusP002Output2571.1
  | 3 => embedPair2542 corrSharedN02700PlusP003Output2571.1
  | 4 => embedPair2542 corrSharedN02700PlusP004Output2571.1
  | 5 => embedPair2542 corrSharedN02700PlusP005Output2571.1
  | 6 => embedPair2542 corrSharedN02700PlusP006Output2571.1
  | 7 => embedPair2542 corrSharedN02700PlusP007Output2571.1
  | 8 => embedPair2542 corrSharedN02700PlusP008Output2571.1
  | 9 => embedPair2542 corrSharedN02700PlusP009Output2571.1
  | 10 => embedPair2542 corrSharedN02700PlusP010Output2571.1
  | 11 => embedPair2542 corrSharedN02700PlusP011Output2571.1
  | 12 => embedPair2542 corrSharedN02700PlusP012Output2571.1
  | 13 => embedPair2542 corrSharedN02700PlusP013Output2571.1
  | 14 => embedPair2542 corrSharedN02700PlusP014Output2571.1
  | 15 => embedPair2542 corrSharedN02700PlusP015Output2571.1
  | 16 => embedPair2542 corrSharedN02700PlusP016Output2571.1
  | 17 => embedPair2542 corrSharedN02700PlusP017Output2571.1
  | 18 => embedPair2542 corrSharedN02700PlusP018Output2571.1
  | 19 => embedPair2542 corrSharedN02700PlusP019Output2571.1
  | 20 => embedPair2542 corrSharedN02700PlusP020Output2571.1
  | 21 => embedPair2542 corrSharedN02700PlusP021Output2571.1
  | 22 => embedPair2542 corrSharedN02700PlusP022Output2571.1
  | 23 => embedPair2542 corrSharedN02700PlusP023Output2571.1
  | 24 => embedPair2542 corrSharedN02700PlusP024Output2571.1
  | 25 => embedPair2542 corrSharedN02700PlusP025Output2571.1
  | 26 => embedPair2542 corrSharedN02700PlusP026Output2571.1
  | 27 => embedPair2542 corrSharedN02700PlusP027Output2571.1
  | 28 => embedPair2542 corrSharedN02700PlusP028Output2571.1
  | 29 => embedPair2542 corrSharedN02700PlusP029Output2571.1
  | _ => 0

noncomputable def corrSharedN02700PlusError2571 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (corrSharedN02700PlusP000Output2571.2 : ℝ)
  | 1 => (corrSharedN02700PlusP001Output2571.2 : ℝ)
  | 2 => (corrSharedN02700PlusP002Output2571.2 : ℝ)
  | 3 => (corrSharedN02700PlusP003Output2571.2 : ℝ)
  | 4 => (corrSharedN02700PlusP004Output2571.2 : ℝ)
  | 5 => (corrSharedN02700PlusP005Output2571.2 : ℝ)
  | 6 => (corrSharedN02700PlusP006Output2571.2 : ℝ)
  | 7 => (corrSharedN02700PlusP007Output2571.2 : ℝ)
  | 8 => (corrSharedN02700PlusP008Output2571.2 : ℝ)
  | 9 => (corrSharedN02700PlusP009Output2571.2 : ℝ)
  | 10 => (corrSharedN02700PlusP010Output2571.2 : ℝ)
  | 11 => (corrSharedN02700PlusP011Output2571.2 : ℝ)
  | 12 => (corrSharedN02700PlusP012Output2571.2 : ℝ)
  | 13 => (corrSharedN02700PlusP013Output2571.2 : ℝ)
  | 14 => (corrSharedN02700PlusP014Output2571.2 : ℝ)
  | 15 => (corrSharedN02700PlusP015Output2571.2 : ℝ)
  | 16 => (corrSharedN02700PlusP016Output2571.2 : ℝ)
  | 17 => (corrSharedN02700PlusP017Output2571.2 : ℝ)
  | 18 => (corrSharedN02700PlusP018Output2571.2 : ℝ)
  | 19 => (corrSharedN02700PlusP019Output2571.2 : ℝ)
  | 20 => (corrSharedN02700PlusP020Output2571.2 : ℝ)
  | 21 => (corrSharedN02700PlusP021Output2571.2 : ℝ)
  | 22 => (corrSharedN02700PlusP022Output2571.2 : ℝ)
  | 23 => (corrSharedN02700PlusP023Output2571.2 : ℝ)
  | 24 => (corrSharedN02700PlusP024Output2571.2 : ℝ)
  | 25 => (corrSharedN02700PlusP025Output2571.2 : ℝ)
  | 26 => (corrSharedN02700PlusP026Output2571.2 : ℝ)
  | 27 => (corrSharedN02700PlusP027Output2571.2 : ℝ)
  | 28 => (corrSharedN02700PlusP028Output2571.2 : ℝ)
  | 29 => (corrSharedN02700PlusP029Output2571.2 : ℝ)
  | _ => 0

theorem corrSharedN02700PlusExp_error2571 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i corrSharedN02700PlusPosition2571 - corrSharedN02700PlusValue2571
            i‖ ≤
            corrSharedN02700PlusError2571 i := by
  fin_cases i
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP000Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP001Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP002Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP003Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP004Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP005Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP006Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP007Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP008Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP009Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP010Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP011Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP012Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP013Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP014Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP015Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP016Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP017Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP018Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP019Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP020Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP021Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP022Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP023Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP024Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP025Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP026Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP027Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP028Error2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP029Error2571

theorem corrSharedN02700PlusUnit_norm2571 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i corrSharedN02700PlusPosition2571‖ ≤ 1 := by
  fin_cases i
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP000Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP001Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP002Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP003Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP004Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP005Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP006Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP007Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP008Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP009Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP010Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP011Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP012Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP013Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP014Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP015Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP016Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP017Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP018Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP019Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP020Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP021Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP022Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP023Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP024Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP025Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP026Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP027Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP028Norm2571
  · simpa only [corrSharedN02700PlusValue2571, corrSharedN02700PlusError2571] using
      corrSharedN02700PlusP029Norm2571

noncomputable def corrSharedN02700PlusSumValue2571 : ℂ := ⟨(((((894734054427158088599176849 *
    10^40
        + 5462649421437713270120562448898983012763) * 10^40
        + 9785946197600510630890032123751724202989) * 10^40
        + 1006084402345803433885212017290571811153) : ℝ) /
        (((1636695303948070935006594848413 * 10^40
        + 7995761083210230215323947416456840480668) * 10^40
        + 9820233727744163504616295207857544334206) * 10^40
        + 3780035504608628272942696526664263794688)),
    (((-(((694460430462488856997425665 * 10^40
        + 2866764136810167307685092685291570097819) * 10^40
        + 5995574123942351200184410561883209546496) * 10^40
        + 3246672045761243722355859344370160735901)) : ℝ) /
        (((1636695303948070935006594848413 * 10^40
        + 7995761083210230215323947416456840480668) * 10^40
        + 9820233727744163504616295207857544334206) * 10^40
        + 3780035504608628272942696526664263794688))⟩

noncomputable def corrSharedN02700PlusUpper2571 : ℝ := ((1384031 : ℝ) /
        2000000000)

theorem corrSharedN02700PlusSum_eq2571 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02700PlusValue2571 i) =
      corrSharedN02700PlusSumValue2571 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        corrSharedN02700PlusValue2571,
      corrSharedN02700PlusSumValue2571, embedPair2542, corrSharedN02700PlusP000Output2571,
      corrSharedN02700PlusP001Output2571,
      corrSharedN02700PlusP002Output2571,
      corrSharedN02700PlusP003Output2571,
      corrSharedN02700PlusP004Output2571,
      corrSharedN02700PlusP005Output2571,
      corrSharedN02700PlusP006Output2571,
      corrSharedN02700PlusP007Output2571,
      corrSharedN02700PlusP008Output2571,
      corrSharedN02700PlusP009Output2571,
      corrSharedN02700PlusP010Output2571,
      corrSharedN02700PlusP011Output2571,
      corrSharedN02700PlusP012Output2571,
      corrSharedN02700PlusP013Output2571,
      corrSharedN02700PlusP014Output2571,
      corrSharedN02700PlusP015Output2571,
      corrSharedN02700PlusP016Output2571,
      corrSharedN02700PlusP017Output2571,
      corrSharedN02700PlusP018Output2571,
      corrSharedN02700PlusP019Output2571,
      corrSharedN02700PlusP020Output2571,
      corrSharedN02700PlusP021Output2571,
      corrSharedN02700PlusP022Output2571,
      corrSharedN02700PlusP023Output2571,
      corrSharedN02700PlusP024Output2571,
      corrSharedN02700PlusP025Output2571,
      corrSharedN02700PlusP026Output2571,
      corrSharedN02700PlusP027Output2571,
      corrSharedN02700PlusP028Output2571,
      corrSharedN02700PlusP029Output2571, Complex.mul_re, Complex.mul_im]

theorem corrSharedN02700PlusSum_norm2571 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02700PlusValue2571 i‖ ≤
      ((3460077 : ℝ) /
        5000000000) := by
  rw [corrSharedN02700PlusSum_eq2571]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [corrSharedN02700PlusSumValue2571]

theorem corrSharedN02700PlusEvaluation_charge2571 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * corrSharedN02700PlusError2571 i) ≤ (1 : ℝ)/10^12
          := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      corrSharedN02700PlusError2571,
      corrSharedN02700PlusP000Output2571,
      corrSharedN02700PlusP001Output2571,
      corrSharedN02700PlusP002Output2571,
      corrSharedN02700PlusP003Output2571,
      corrSharedN02700PlusP004Output2571,
      corrSharedN02700PlusP005Output2571,
      corrSharedN02700PlusP006Output2571,
      corrSharedN02700PlusP007Output2571,
      corrSharedN02700PlusP008Output2571,
      corrSharedN02700PlusP009Output2571,
      corrSharedN02700PlusP010Output2571,
      corrSharedN02700PlusP011Output2571,
      corrSharedN02700PlusP012Output2571,
      corrSharedN02700PlusP013Output2571,
      corrSharedN02700PlusP014Output2571,
      corrSharedN02700PlusP015Output2571,
      corrSharedN02700PlusP016Output2571,
      corrSharedN02700PlusP017Output2571,
      corrSharedN02700PlusP018Output2571,
      corrSharedN02700PlusP019Output2571,
      corrSharedN02700PlusP020Output2571,
      corrSharedN02700PlusP021Output2571,
      corrSharedN02700PlusP022Output2571,
      corrSharedN02700PlusP023Output2571,
      corrSharedN02700PlusP024Output2571,
      corrSharedN02700PlusP025Output2571,
      corrSharedN02700PlusP026Output2571,
      corrSharedN02700PlusP027Output2571,
      corrSharedN02700PlusP028Output2571,
      corrSharedN02700PlusP029Output2571]

theorem corrSharedN02700PlusSigned_le2571 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 corrSharedN02700PlusPosition2571 ≤ corrSharedN02700PlusUpper2571 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i corrSharedN02700PlusPosition2571‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02700PlusValue2571 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * corrSharedN02700PlusError2571 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (corrSharedN02700PlusExp_error2571 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i corrSharedN02700PlusPosition2571‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (corrSharedN02700PlusUnit_norm2571 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i corrSharedN02700PlusPosition2571‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 corrSharedN02700PlusUpper2571
  linarith [corrSharedN02700PlusSum_norm2571, corrSharedN02700PlusEvaluation_charge2571]

theorem corrSharedN02700PlusPhysical_le2571 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 corrSharedN02700PlusPosition2571‖ ≤
      corrSharedN02700PlusUpper2571 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        corrSharedN02700PlusPosition2571
  simpa only [iteratedDeriv_zero] using h.trans corrSharedN02700PlusSigned_le2571

theorem corrSharedN02700PlusGrid2571 :
    -stripRadius2303 + (2700 : ℝ)*(2*stripRadius2303/10240) = corrSharedN02700PlusPosition2571 :=
        by
  norm_num [stripRadius2303, corrSharedN02700PlusPosition2571]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrSharedN02700PlusSigned_le2571
#print axioms ConnesWeilRH.Dev.corrSharedN02700PlusPhysical_le2571
