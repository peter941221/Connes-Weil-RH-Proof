import ConnesWeilRH.Dev.C1RouteAKernelN02700Minus2555
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def corrSharedN02700MinusPosition2570 : ℝ := (((-7929856121) : ℝ) /
        2560000000)

def corrSharedN02700MinusP000Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP000Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP000Output2570.1‖ ≤ (corrSharedN02700MinusP000Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP000BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP000Output2570,
    kernelN02700MinusP000Center2555, kernelN02700MinusP000Error2555, embedPair2542]

theorem corrSharedN02700MinusP000Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP000Output2570.1) + embedPair2542
            corrSharedN02700MinusP000Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP000Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP000Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP000Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP000Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP000Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP000Output2570, pairMagnitude2542]

def corrSharedN02700MinusP001Output2570 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02700MinusP001Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP001Output2570.1‖ ≤ (corrSharedN02700MinusP001Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP001BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP001Output2570,
    kernelN02700MinusP001Center2555, kernelN02700MinusP001Error2555, embedPair2542]

theorem corrSharedN02700MinusP001Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP001Output2570.1) + embedPair2542
            corrSharedN02700MinusP001Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP001Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP001Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP001Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP001Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP001Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP001Output2570, pairMagnitude2542]

def corrSharedN02700MinusP002Output2570 : RatState2542 :=
  (((((-236687586501322481317) : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    (((-10235158114556736630683) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((23242280564835055193 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem corrSharedN02700MinusP002Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP002Output2570.1‖ ≤ (corrSharedN02700MinusP002Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP002BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP002Output2570,
    kernelN02700MinusP002Center2555, kernelN02700MinusP002Error2555, embedPair2542]

theorem corrSharedN02700MinusP002Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP002Output2570.1) + embedPair2542
            corrSharedN02700MinusP002Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP002Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP002Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP002Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP002Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP002Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP002Output2570, pairMagnitude2542]

def corrSharedN02700MinusP003Output2570 : RatState2542 :=
  (((((-67562655288918125376430023877) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-45650528571176392534168394947) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((48559493963991329543302431 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336)))

theorem corrSharedN02700MinusP003Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP003Output2570.1‖ ≤ (corrSharedN02700MinusP003Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP003BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP003Output2570,
    kernelN02700MinusP003Center2555, kernelN02700MinusP003Error2555, embedPair2542]

theorem corrSharedN02700MinusP003Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP003Output2570.1) + embedPair2542
            corrSharedN02700MinusP003Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP003Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP003Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP003Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP003Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP003Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP003Output2570, pairMagnitude2542]

def corrSharedN02700MinusP004Output2570 : RatState2542 :=
  (((((-68389271845661481738864442245855) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((92418108643056889386327940952689 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((383779637246708834189989500561 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02700MinusP004Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP004Output2570.1‖ ≤ (corrSharedN02700MinusP004Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP004BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP004Output2570,
    kernelN02700MinusP004Center2555, kernelN02700MinusP004Error2555, embedPair2542]

theorem corrSharedN02700MinusP004Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP004Output2570.1) + embedPair2542
            corrSharedN02700MinusP004Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP004Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP004Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP004Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP004Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP004Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP004Output2570, pairMagnitude2542]

def corrSharedN02700MinusP005Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP005Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP005Output2570.1‖ ≤ (corrSharedN02700MinusP005Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP005BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP005Output2570,
    kernelN02700MinusP005Center2555, kernelN02700MinusP005Error2555, embedPair2542]

theorem corrSharedN02700MinusP005Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP005Output2570.1) + embedPair2542
            corrSharedN02700MinusP005Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP005Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP005Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP005Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP005Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP005Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP005Output2570, pairMagnitude2542]

def corrSharedN02700MinusP006Output2570 : RatState2542 :=
  ((((19504508082407141 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((7069434267121 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02700MinusP006Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP006Output2570.1‖ ≤ (corrSharedN02700MinusP006Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP006BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP006Output2570,
    kernelN02700MinusP006Center2555, kernelN02700MinusP006Error2555, embedPair2542]

theorem corrSharedN02700MinusP006Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP006Output2570.1) + embedPair2542
            corrSharedN02700MinusP006Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP006Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP006Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP006Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP006Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP006Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP006Output2570, pairMagnitude2542]

def corrSharedN02700MinusP007Output2570 : RatState2542 :=
  ((((227161576196330745979291438463 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((31448282402248334335030421 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02700MinusP007Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP007Output2570.1‖ ≤ (corrSharedN02700MinusP007Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP007BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP007Output2570,
    kernelN02700MinusP007Center2555, kernelN02700MinusP007Error2555, embedPair2542]

theorem corrSharedN02700MinusP007Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP007Output2570.1) + embedPair2542
            corrSharedN02700MinusP007Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP007Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP007Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP007Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP007Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP007Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP007Output2570, pairMagnitude2542]

def corrSharedN02700MinusP008Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP008Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP008Output2570.1‖ ≤ (corrSharedN02700MinusP008Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP008BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP008Output2570,
    kernelN02700MinusP008Center2555, kernelN02700MinusP008Error2555, embedPair2542]

theorem corrSharedN02700MinusP008Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP008Output2570.1) + embedPair2542
            corrSharedN02700MinusP008Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP008Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP008Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP008Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP008Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP008Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP008Output2570, pairMagnitude2542]

def corrSharedN02700MinusP009Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP009Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP009Output2570.1‖ ≤ (corrSharedN02700MinusP009Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP009BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP009Output2570,
    kernelN02700MinusP009Center2555, kernelN02700MinusP009Error2555, embedPair2542]

theorem corrSharedN02700MinusP009Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP009Output2570.1) + embedPair2542
            corrSharedN02700MinusP009Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP009Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP009Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP009Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP009Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP009Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP009Output2570, pairMagnitude2542]

def corrSharedN02700MinusP010Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP010Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP010Output2570.1‖ ≤ (corrSharedN02700MinusP010Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP010BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP010Output2570,
    kernelN02700MinusP010Center2555, kernelN02700MinusP010Error2555, embedPair2542]

theorem corrSharedN02700MinusP010Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP010Output2570.1) + embedPair2542
            corrSharedN02700MinusP010Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP010Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP010Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP010Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP010Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP010Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP010Output2570, pairMagnitude2542]

def corrSharedN02700MinusP011Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP011Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP011Output2570.1‖ ≤ (corrSharedN02700MinusP011Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP011BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP011Output2570,
    kernelN02700MinusP011Center2555, kernelN02700MinusP011Error2555, embedPair2542]

theorem corrSharedN02700MinusP011Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP011Output2570.1) + embedPair2542
            corrSharedN02700MinusP011Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP011Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP011Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP011Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP011Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP011Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP011Output2570, pairMagnitude2542]

def corrSharedN02700MinusP012Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP012Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP012Output2570.1‖ ≤ (corrSharedN02700MinusP012Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP012BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP012Output2570,
    kernelN02700MinusP012Center2555, kernelN02700MinusP012Error2555, embedPair2542]

theorem corrSharedN02700MinusP012Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP012Output2570.1) + embedPair2542
            corrSharedN02700MinusP012Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP012Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP012Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP012Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP012Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP012Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP012Output2570, pairMagnitude2542]

def corrSharedN02700MinusP013Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP013Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP013Output2570.1‖ ≤ (corrSharedN02700MinusP013Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP013BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP013Output2570,
    kernelN02700MinusP013Center2555, kernelN02700MinusP013Error2555, embedPair2542]

theorem corrSharedN02700MinusP013Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP013Output2570.1) + embedPair2542
            corrSharedN02700MinusP013Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP013Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP013Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP013Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP013Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP013Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP013Output2570, pairMagnitude2542]

def corrSharedN02700MinusP014Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP014Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP014Output2570.1‖ ≤ (corrSharedN02700MinusP014Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP014BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP014Output2570,
    kernelN02700MinusP014Center2555, kernelN02700MinusP014Error2555, embedPair2542]

theorem corrSharedN02700MinusP014Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP014Output2570.1) + embedPair2542
            corrSharedN02700MinusP014Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP014Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP014Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP014Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP014Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP014Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP014Output2570, pairMagnitude2542]

def corrSharedN02700MinusP015Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP015Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP015Output2570.1‖ ≤ (corrSharedN02700MinusP015Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP015BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP015Output2570,
    kernelN02700MinusP015Center2555, kernelN02700MinusP015Error2555, embedPair2542]

theorem corrSharedN02700MinusP015Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP015Output2570.1) + embedPair2542
            corrSharedN02700MinusP015Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP015Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP015Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP015Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP015Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP015Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP015Output2570, pairMagnitude2542]

def corrSharedN02700MinusP016Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP016Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP016Output2570.1‖ ≤ (corrSharedN02700MinusP016Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP016BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP016Output2570,
    kernelN02700MinusP016Center2555, kernelN02700MinusP016Error2555, embedPair2542]

theorem corrSharedN02700MinusP016Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP016Output2570.1) + embedPair2542
            corrSharedN02700MinusP016Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP016Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP016Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP016Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP016Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP016Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP016Output2570, pairMagnitude2542]

def corrSharedN02700MinusP017Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP017Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP017Output2570.1‖ ≤ (corrSharedN02700MinusP017Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP017BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP017Output2570,
    kernelN02700MinusP017Center2555, kernelN02700MinusP017Error2555, embedPair2542]

theorem corrSharedN02700MinusP017Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP017Output2570.1) + embedPair2542
            corrSharedN02700MinusP017Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP017Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP017Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP017Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP017Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP017Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP017Output2570, pairMagnitude2542]

def corrSharedN02700MinusP018Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP018Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP018Output2570.1‖ ≤ (corrSharedN02700MinusP018Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP018BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP018Output2570,
    kernelN02700MinusP018Center2555, kernelN02700MinusP018Error2555, embedPair2542]

theorem corrSharedN02700MinusP018Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP018Output2570.1) + embedPair2542
            corrSharedN02700MinusP018Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP018Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP018Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP018Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP018Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP018Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP018Output2570, pairMagnitude2542]

def corrSharedN02700MinusP019Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP019Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP019Output2570.1‖ ≤ (corrSharedN02700MinusP019Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP019BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP019Output2570,
    kernelN02700MinusP019Center2555, kernelN02700MinusP019Error2555, embedPair2542]

theorem corrSharedN02700MinusP019Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP019Output2570.1) + embedPair2542
            corrSharedN02700MinusP019Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP019Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP019Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP019Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP019Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP019Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP019Output2570, pairMagnitude2542]

def corrSharedN02700MinusP020Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP020Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP020Output2570.1‖ ≤ (corrSharedN02700MinusP020Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP020BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP020Output2570,
    kernelN02700MinusP020Center2555, kernelN02700MinusP020Error2555, embedPair2542]

theorem corrSharedN02700MinusP020Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP020Output2570.1) + embedPair2542
            corrSharedN02700MinusP020Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP020Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP020Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP020Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP020Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP020Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP020Output2570, pairMagnitude2542]

def corrSharedN02700MinusP021Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP021Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP021Output2570.1‖ ≤ (corrSharedN02700MinusP021Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP021BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP021Output2570,
    kernelN02700MinusP021Center2555, kernelN02700MinusP021Error2555, embedPair2542]

theorem corrSharedN02700MinusP021Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP021Output2570.1) + embedPair2542
            corrSharedN02700MinusP021Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP021Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP021Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP021Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP021Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP021Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP021Output2570, pairMagnitude2542]

def corrSharedN02700MinusP022Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP022Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP022Output2570.1‖ ≤ (corrSharedN02700MinusP022Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP022BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP022Output2570,
    kernelN02700MinusP022Center2555, kernelN02700MinusP022Error2555, embedPair2542]

theorem corrSharedN02700MinusP022Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP022Output2570.1) + embedPair2542
            corrSharedN02700MinusP022Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP022Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP022Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP022Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP022Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP022Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP022Output2570, pairMagnitude2542]

def corrSharedN02700MinusP023Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP023Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP023Output2570.1‖ ≤ (corrSharedN02700MinusP023Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP023BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP023Output2570,
    kernelN02700MinusP023Center2555, kernelN02700MinusP023Error2555, embedPair2542]

theorem corrSharedN02700MinusP023Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP023Output2570.1) + embedPair2542
            corrSharedN02700MinusP023Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP023Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP023Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP023Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP023Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP023Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP023Output2570, pairMagnitude2542]

def corrSharedN02700MinusP024Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP024Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP024Output2570.1‖ ≤ (corrSharedN02700MinusP024Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP024BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP024Output2570,
    kernelN02700MinusP024Center2555, kernelN02700MinusP024Error2555, embedPair2542]

theorem corrSharedN02700MinusP024Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP024Output2570.1) + embedPair2542
            corrSharedN02700MinusP024Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP024Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP024Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP024Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP024Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP024Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP024Output2570, pairMagnitude2542]

def corrSharedN02700MinusP025Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP025Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP025Output2570.1‖ ≤ (corrSharedN02700MinusP025Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP025BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP025Output2570,
    kernelN02700MinusP025Center2555, kernelN02700MinusP025Error2555, embedPair2542]

theorem corrSharedN02700MinusP025Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP025Output2570.1) + embedPair2542
            corrSharedN02700MinusP025Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP025Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP025Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP025Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP025Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP025Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP025Output2570, pairMagnitude2542]

def corrSharedN02700MinusP026Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP026Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP026Output2570.1‖ ≤ (corrSharedN02700MinusP026Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP026BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP026Output2570,
    kernelN02700MinusP026Center2555, kernelN02700MinusP026Error2555, embedPair2542]

theorem corrSharedN02700MinusP026Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP026Output2570.1) + embedPair2542
            corrSharedN02700MinusP026Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP026Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP026Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP026Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP026Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP026Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP026Output2570, pairMagnitude2542]

def corrSharedN02700MinusP027Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP027Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP027Output2570.1‖ ≤ (corrSharedN02700MinusP027Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP027BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP027Output2570,
    kernelN02700MinusP027Center2555, kernelN02700MinusP027Error2555, embedPair2542]

theorem corrSharedN02700MinusP027Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP027Output2570.1) + embedPair2542
            corrSharedN02700MinusP027Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP027Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP027Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP027Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP027Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP027Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP027Output2570, pairMagnitude2542]

def corrSharedN02700MinusP028Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP028Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP028Output2570.1‖ ≤ (corrSharedN02700MinusP028Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP028BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP028Output2570,
    kernelN02700MinusP028Center2555, kernelN02700MinusP028Error2555, embedPair2542]

theorem corrSharedN02700MinusP028Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP028Output2570.1) + embedPair2542
            corrSharedN02700MinusP028Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP028Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP028Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP028Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP028Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP028Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP028Output2570, pairMagnitude2542]

def corrSharedN02700MinusP029Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02700MinusP029Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP029Output2570.1‖ ≤ (corrSharedN02700MinusP029Output2570.2 : ℝ)
                := by
  have h := kernelN02700MinusP029BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02700MinusPosition2570, kernelN02700MinusPosition2555,
      corrSharedN02700MinusP029Output2570,
    kernelN02700MinusP029Center2555, kernelN02700MinusP029Error2555, embedPair2542]

theorem corrSharedN02700MinusP029Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02700MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP029Output2570.1) + embedPair2542
            corrSharedN02700MinusP029Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02700MinusPosition2570 - embedPair2542
            corrSharedN02700MinusP029Output2570.1‖ + ‖embedPair2542
            corrSharedN02700MinusP029Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02700MinusP029Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02700MinusP029Output2570.1 : ℝ) :=
      add_le_add corrSharedN02700MinusP029Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02700MinusP029Output2570, pairMagnitude2542]

noncomputable def corrSharedN02700MinusValue2570 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 corrSharedN02700MinusP000Output2570.1
  | 1 => embedPair2542 corrSharedN02700MinusP001Output2570.1
  | 2 => embedPair2542 corrSharedN02700MinusP002Output2570.1
  | 3 => embedPair2542 corrSharedN02700MinusP003Output2570.1
  | 4 => embedPair2542 corrSharedN02700MinusP004Output2570.1
  | 5 => embedPair2542 corrSharedN02700MinusP005Output2570.1
  | 6 => embedPair2542 corrSharedN02700MinusP006Output2570.1
  | 7 => embedPair2542 corrSharedN02700MinusP007Output2570.1
  | 8 => embedPair2542 corrSharedN02700MinusP008Output2570.1
  | 9 => embedPair2542 corrSharedN02700MinusP009Output2570.1
  | 10 => embedPair2542 corrSharedN02700MinusP010Output2570.1
  | 11 => embedPair2542 corrSharedN02700MinusP011Output2570.1
  | 12 => embedPair2542 corrSharedN02700MinusP012Output2570.1
  | 13 => embedPair2542 corrSharedN02700MinusP013Output2570.1
  | 14 => embedPair2542 corrSharedN02700MinusP014Output2570.1
  | 15 => embedPair2542 corrSharedN02700MinusP015Output2570.1
  | 16 => embedPair2542 corrSharedN02700MinusP016Output2570.1
  | 17 => embedPair2542 corrSharedN02700MinusP017Output2570.1
  | 18 => embedPair2542 corrSharedN02700MinusP018Output2570.1
  | 19 => embedPair2542 corrSharedN02700MinusP019Output2570.1
  | 20 => embedPair2542 corrSharedN02700MinusP020Output2570.1
  | 21 => embedPair2542 corrSharedN02700MinusP021Output2570.1
  | 22 => embedPair2542 corrSharedN02700MinusP022Output2570.1
  | 23 => embedPair2542 corrSharedN02700MinusP023Output2570.1
  | 24 => embedPair2542 corrSharedN02700MinusP024Output2570.1
  | 25 => embedPair2542 corrSharedN02700MinusP025Output2570.1
  | 26 => embedPair2542 corrSharedN02700MinusP026Output2570.1
  | 27 => embedPair2542 corrSharedN02700MinusP027Output2570.1
  | 28 => embedPair2542 corrSharedN02700MinusP028Output2570.1
  | 29 => embedPair2542 corrSharedN02700MinusP029Output2570.1
  | _ => 0

noncomputable def corrSharedN02700MinusError2570 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (corrSharedN02700MinusP000Output2570.2 : ℝ)
  | 1 => (corrSharedN02700MinusP001Output2570.2 : ℝ)
  | 2 => (corrSharedN02700MinusP002Output2570.2 : ℝ)
  | 3 => (corrSharedN02700MinusP003Output2570.2 : ℝ)
  | 4 => (corrSharedN02700MinusP004Output2570.2 : ℝ)
  | 5 => (corrSharedN02700MinusP005Output2570.2 : ℝ)
  | 6 => (corrSharedN02700MinusP006Output2570.2 : ℝ)
  | 7 => (corrSharedN02700MinusP007Output2570.2 : ℝ)
  | 8 => (corrSharedN02700MinusP008Output2570.2 : ℝ)
  | 9 => (corrSharedN02700MinusP009Output2570.2 : ℝ)
  | 10 => (corrSharedN02700MinusP010Output2570.2 : ℝ)
  | 11 => (corrSharedN02700MinusP011Output2570.2 : ℝ)
  | 12 => (corrSharedN02700MinusP012Output2570.2 : ℝ)
  | 13 => (corrSharedN02700MinusP013Output2570.2 : ℝ)
  | 14 => (corrSharedN02700MinusP014Output2570.2 : ℝ)
  | 15 => (corrSharedN02700MinusP015Output2570.2 : ℝ)
  | 16 => (corrSharedN02700MinusP016Output2570.2 : ℝ)
  | 17 => (corrSharedN02700MinusP017Output2570.2 : ℝ)
  | 18 => (corrSharedN02700MinusP018Output2570.2 : ℝ)
  | 19 => (corrSharedN02700MinusP019Output2570.2 : ℝ)
  | 20 => (corrSharedN02700MinusP020Output2570.2 : ℝ)
  | 21 => (corrSharedN02700MinusP021Output2570.2 : ℝ)
  | 22 => (corrSharedN02700MinusP022Output2570.2 : ℝ)
  | 23 => (corrSharedN02700MinusP023Output2570.2 : ℝ)
  | 24 => (corrSharedN02700MinusP024Output2570.2 : ℝ)
  | 25 => (corrSharedN02700MinusP025Output2570.2 : ℝ)
  | 26 => (corrSharedN02700MinusP026Output2570.2 : ℝ)
  | 27 => (corrSharedN02700MinusP027Output2570.2 : ℝ)
  | 28 => (corrSharedN02700MinusP028Output2570.2 : ℝ)
  | 29 => (corrSharedN02700MinusP029Output2570.2 : ℝ)
  | _ => 0

theorem corrSharedN02700MinusExp_error2570 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02700MinusPosition2570 -
            corrSharedN02700MinusValue2570 i‖
            ≤ corrSharedN02700MinusError2570 i := by
  fin_cases i
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP000Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP001Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP002Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP003Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP004Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP005Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP006Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP007Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP008Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP009Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP010Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP011Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP012Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP013Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP014Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP015Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP016Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP017Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP018Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP019Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP020Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP021Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP022Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP023Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP024Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP025Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP026Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP027Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP028Error2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP029Error2570

theorem corrSharedN02700MinusUnit_norm2570 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02700MinusPosition2570‖ ≤ 1 := by
  fin_cases i
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP000Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP001Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP002Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP003Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP004Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP005Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP006Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP007Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP008Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP009Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP010Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP011Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP012Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP013Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP014Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP015Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP016Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP017Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP018Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP019Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP020Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP021Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP022Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP023Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP024Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP025Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP026Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP027Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP028Norm2570
  · simpa only [corrSharedN02700MinusValue2570, corrSharedN02700MinusError2570] using
      corrSharedN02700MinusP029Norm2570

noncomputable def corrSharedN02700MinusSumValue2570 : ℂ := ⟨(((((19813654010149859586439039169 *
    10^40
        + 5748732704623307954414351769273439651781) * 10^40
        + 7130240743188419013304490757149966061138) * 10^40
        + 1296120597417893706461196395970475026081) : ℝ) /
        (((1636695303948070935006594848413 * 10^40
        + 7995761083210230215323947416456840480668) * 10^40
        + 9820233727744163504616295207857544334206) * 10^40
        + 3780035504608628272942696526664263794688)),
    (((-(((7689323226739717243747067182 * 10^40
        + 9753701212549312302622954539188226214610) * 10^40
        + 767251348053722031416895313959349028170) * 10^40
        + 6651723133930020937973742368292051910441)) : ℝ) /
        (((818347651974035467503297424206 * 10^40
        + 8997880541605115107661973708228420240334) * 10^40
        + 4910116863872081752308147603928772167103) * 10^40
        + 1890017752304314136471348263332131897344))⟩

noncomputable def corrSharedN02700MinusUpper2570 : ℝ := ((153245019 : ℝ) /
        10000000000)

theorem corrSharedN02700MinusSum_eq2570 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02700MinusValue2570 i) =
      corrSharedN02700MinusSumValue2570 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        corrSharedN02700MinusValue2570,
      corrSharedN02700MinusSumValue2570, embedPair2542, corrSharedN02700MinusP000Output2570,
      corrSharedN02700MinusP001Output2570,
      corrSharedN02700MinusP002Output2570,
      corrSharedN02700MinusP003Output2570,
      corrSharedN02700MinusP004Output2570,
      corrSharedN02700MinusP005Output2570,
      corrSharedN02700MinusP006Output2570,
      corrSharedN02700MinusP007Output2570,
      corrSharedN02700MinusP008Output2570,
      corrSharedN02700MinusP009Output2570,
      corrSharedN02700MinusP010Output2570,
      corrSharedN02700MinusP011Output2570,
      corrSharedN02700MinusP012Output2570,
      corrSharedN02700MinusP013Output2570,
      corrSharedN02700MinusP014Output2570,
      corrSharedN02700MinusP015Output2570,
      corrSharedN02700MinusP016Output2570,
      corrSharedN02700MinusP017Output2570,
      corrSharedN02700MinusP018Output2570,
      corrSharedN02700MinusP019Output2570,
      corrSharedN02700MinusP020Output2570,
      corrSharedN02700MinusP021Output2570,
      corrSharedN02700MinusP022Output2570,
      corrSharedN02700MinusP023Output2570,
      corrSharedN02700MinusP024Output2570,
      corrSharedN02700MinusP025Output2570,
      corrSharedN02700MinusP026Output2570,
      corrSharedN02700MinusP027Output2570,
      corrSharedN02700MinusP028Output2570,
      corrSharedN02700MinusP029Output2570, Complex.mul_re, Complex.mul_im]

theorem corrSharedN02700MinusSum_norm2570 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02700MinusValue2570 i‖ ≤
      ((76622509 : ℝ) /
        5000000000) := by
  rw [corrSharedN02700MinusSum_eq2570]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [corrSharedN02700MinusSumValue2570]

theorem corrSharedN02700MinusEvaluation_charge2570 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * corrSharedN02700MinusError2570 i) ≤ (1 :
          ℝ)/10^12
          := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      corrSharedN02700MinusError2570,
      corrSharedN02700MinusP000Output2570,
      corrSharedN02700MinusP001Output2570,
      corrSharedN02700MinusP002Output2570,
      corrSharedN02700MinusP003Output2570,
      corrSharedN02700MinusP004Output2570,
      corrSharedN02700MinusP005Output2570,
      corrSharedN02700MinusP006Output2570,
      corrSharedN02700MinusP007Output2570,
      corrSharedN02700MinusP008Output2570,
      corrSharedN02700MinusP009Output2570,
      corrSharedN02700MinusP010Output2570,
      corrSharedN02700MinusP011Output2570,
      corrSharedN02700MinusP012Output2570,
      corrSharedN02700MinusP013Output2570,
      corrSharedN02700MinusP014Output2570,
      corrSharedN02700MinusP015Output2570,
      corrSharedN02700MinusP016Output2570,
      corrSharedN02700MinusP017Output2570,
      corrSharedN02700MinusP018Output2570,
      corrSharedN02700MinusP019Output2570,
      corrSharedN02700MinusP020Output2570,
      corrSharedN02700MinusP021Output2570,
      corrSharedN02700MinusP022Output2570,
      corrSharedN02700MinusP023Output2570,
      corrSharedN02700MinusP024Output2570,
      corrSharedN02700MinusP025Output2570,
      corrSharedN02700MinusP026Output2570,
      corrSharedN02700MinusP027Output2570,
      corrSharedN02700MinusP028Output2570,
      corrSharedN02700MinusP029Output2570]

theorem corrSharedN02700MinusSigned_le2570 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 corrSharedN02700MinusPosition2570 ≤ corrSharedN02700MinusUpper2570 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02700MinusPosition2570‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02700MinusValue2570 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * corrSharedN02700MinusError2570 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (corrSharedN02700MinusExp_error2570 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02700MinusPosition2570‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (corrSharedN02700MinusUnit_norm2570 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02700MinusPosition2570‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 corrSharedN02700MinusUpper2570
  linarith [corrSharedN02700MinusSum_norm2570, corrSharedN02700MinusEvaluation_charge2570]

theorem corrSharedN02700MinusPhysical_le2570 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 corrSharedN02700MinusPosition2570‖ ≤
      corrSharedN02700MinusUpper2570 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        corrSharedN02700MinusPosition2570
  simpa only [iteratedDeriv_zero] using h.trans corrSharedN02700MinusSigned_le2570

theorem corrSharedN02700MinusGrid2570 :
    -stripRadius2303 + (2700 : ℝ)*(2*stripRadius2303/10240) = corrSharedN02700MinusPosition2570 :=
        by
  norm_num [stripRadius2303, corrSharedN02700MinusPosition2570]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrSharedN02700MinusSigned_le2570
#print axioms ConnesWeilRH.Dev.corrSharedN02700MinusPhysical_le2570
