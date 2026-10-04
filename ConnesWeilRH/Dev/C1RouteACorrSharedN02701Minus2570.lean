import ConnesWeilRH.Dev.C1RouteAKernelN02701Minus2555
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def corrSharedN02701MinusPosition2570 : ℝ := (((-158531586419) : ℝ) /
        51200000000)

def corrSharedN02701MinusP000Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02701MinusP000Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP000Output2570.1‖ ≤ (corrSharedN02701MinusP000Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP000BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP000Output2570,
    kernelN02701MinusP000Center2555, kernelN02701MinusP000Error2555, embedPair2542]

theorem corrSharedN02701MinusP000Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP000Output2570.1) + embedPair2542
            corrSharedN02701MinusP000Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP000Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP000Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP000Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP000Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP000Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP000Output2570, pairMagnitude2542]

def corrSharedN02701MinusP001Output2570 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP001Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP001Output2570.1‖ ≤ (corrSharedN02701MinusP001Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP001BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP001Output2570,
    kernelN02701MinusP001Center2555, kernelN02701MinusP001Error2555, embedPair2542]

theorem corrSharedN02701MinusP001Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP001Output2570.1) + embedPair2542
            corrSharedN02701MinusP001Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP001Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP001Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP001Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP001Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP001Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP001Output2570, pairMagnitude2542]

def corrSharedN02701MinusP002Output2570 : RatState2542 :=
  (((((-7432742102829368094385) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-11177578774756275941739) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((49382499124458385033 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP002Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP002Output2570.1‖ ≤ (corrSharedN02701MinusP002Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP002BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP002Output2570,
    kernelN02701MinusP002Center2555, kernelN02701MinusP002Error2555, embedPair2542]

theorem corrSharedN02701MinusP002Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP002Output2570.1) + embedPair2542
            corrSharedN02701MinusP002Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP002Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP002Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP002Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP002Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP002Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP002Output2570, pairMagnitude2542]

def corrSharedN02701MinusP003Output2570 : RatState2542 :=
  (((((-128031342998015805707829314715) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-192537343849641036358254016761) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((797028780675931752600253645 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP003Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP003Output2570.1‖ ≤ (corrSharedN02701MinusP003Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP003BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP003Output2570,
    kernelN02701MinusP003Center2555, kernelN02701MinusP003Error2555, embedPair2542]

theorem corrSharedN02701MinusP003Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP003Output2570.1) + embedPair2542
            corrSharedN02701MinusP003Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP003Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP003Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP003Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP003Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP003Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP003Output2570, pairMagnitude2542]

def corrSharedN02701MinusP004Output2570 : RatState2542 :=
  (((((-64207546511769766768481979511471) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((96557219279266825819155349428839 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((97529468585144800089090291783 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem corrSharedN02701MinusP004Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP004Output2570.1‖ ≤ (corrSharedN02701MinusP004Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP004BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP004Output2570,
    kernelN02701MinusP004Center2555, kernelN02701MinusP004Error2555, embedPair2542]

theorem corrSharedN02701MinusP004Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP004Output2570.1) + embedPair2542
            corrSharedN02701MinusP004Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP004Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP004Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP004Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP004Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP004Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP004Output2570, pairMagnitude2542]

def corrSharedN02701MinusP005Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02701MinusP005Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP005Output2570.1‖ ≤ (corrSharedN02701MinusP005Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP005BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP005Output2570,
    kernelN02701MinusP005Center2555, kernelN02701MinusP005Error2555, embedPair2542]

theorem corrSharedN02701MinusP005Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP005Output2570.1) + embedPair2542
            corrSharedN02701MinusP005Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP005Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP005Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP005Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP005Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP005Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP005Output2570, pairMagnitude2542]

def corrSharedN02701MinusP006Output2570 : RatState2542 :=
  ((((21384329496406693 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((3767500786445 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem corrSharedN02701MinusP006Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP006Output2570.1‖ ≤ (corrSharedN02701MinusP006Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP006BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP006Output2570,
    kernelN02701MinusP006Center2555, kernelN02701MinusP006Error2555, embedPair2542]

theorem corrSharedN02701MinusP006Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP006Output2570.1) + embedPair2542
            corrSharedN02701MinusP006Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP006Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP006Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP006Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP006Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP006Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP006Output2570, pairMagnitude2542]

def corrSharedN02701MinusP007Output2570 : RatState2542 :=
  ((((231219924674649256075727664923 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((16000632657409328590635391 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem corrSharedN02701MinusP007Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP007Output2570.1‖ ≤ (corrSharedN02701MinusP007Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP007BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP007Output2570,
    kernelN02701MinusP007Center2555, kernelN02701MinusP007Error2555, embedPair2542]

theorem corrSharedN02701MinusP007Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP007Output2570.1) + embedPair2542
            corrSharedN02701MinusP007Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP007Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP007Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP007Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP007Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP007Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP007Output2570, pairMagnitude2542]

def corrSharedN02701MinusP008Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP008Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP008Output2570.1‖ ≤ (corrSharedN02701MinusP008Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP008BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP008Output2570,
    kernelN02701MinusP008Center2555, kernelN02701MinusP008Error2555, embedPair2542]

theorem corrSharedN02701MinusP008Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP008Output2570.1) + embedPair2542
            corrSharedN02701MinusP008Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP008Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP008Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP008Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP008Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP008Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP008Output2570, pairMagnitude2542]

def corrSharedN02701MinusP009Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP009Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP009Output2570.1‖ ≤ (corrSharedN02701MinusP009Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP009BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP009Output2570,
    kernelN02701MinusP009Center2555, kernelN02701MinusP009Error2555, embedPair2542]

theorem corrSharedN02701MinusP009Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP009Output2570.1) + embedPair2542
            corrSharedN02701MinusP009Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP009Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP009Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP009Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP009Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP009Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP009Output2570, pairMagnitude2542]

def corrSharedN02701MinusP010Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP010Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP010Output2570.1‖ ≤ (corrSharedN02701MinusP010Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP010BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP010Output2570,
    kernelN02701MinusP010Center2555, kernelN02701MinusP010Error2555, embedPair2542]

theorem corrSharedN02701MinusP010Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP010Output2570.1) + embedPair2542
            corrSharedN02701MinusP010Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP010Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP010Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP010Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP010Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP010Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP010Output2570, pairMagnitude2542]

def corrSharedN02701MinusP011Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP011Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP011Output2570.1‖ ≤ (corrSharedN02701MinusP011Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP011BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP011Output2570,
    kernelN02701MinusP011Center2555, kernelN02701MinusP011Error2555, embedPair2542]

theorem corrSharedN02701MinusP011Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP011Output2570.1) + embedPair2542
            corrSharedN02701MinusP011Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP011Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP011Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP011Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP011Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP011Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP011Output2570, pairMagnitude2542]

def corrSharedN02701MinusP012Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP012Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP012Output2570.1‖ ≤ (corrSharedN02701MinusP012Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP012BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP012Output2570,
    kernelN02701MinusP012Center2555, kernelN02701MinusP012Error2555, embedPair2542]

theorem corrSharedN02701MinusP012Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP012Output2570.1) + embedPair2542
            corrSharedN02701MinusP012Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP012Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP012Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP012Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP012Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP012Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP012Output2570, pairMagnitude2542]

def corrSharedN02701MinusP013Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP013Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP013Output2570.1‖ ≤ (corrSharedN02701MinusP013Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP013BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP013Output2570,
    kernelN02701MinusP013Center2555, kernelN02701MinusP013Error2555, embedPair2542]

theorem corrSharedN02701MinusP013Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP013Output2570.1) + embedPair2542
            corrSharedN02701MinusP013Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP013Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP013Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP013Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP013Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP013Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP013Output2570, pairMagnitude2542]

def corrSharedN02701MinusP014Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP014Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP014Output2570.1‖ ≤ (corrSharedN02701MinusP014Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP014BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP014Output2570,
    kernelN02701MinusP014Center2555, kernelN02701MinusP014Error2555, embedPair2542]

theorem corrSharedN02701MinusP014Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP014Output2570.1) + embedPair2542
            corrSharedN02701MinusP014Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP014Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP014Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP014Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP014Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP014Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP014Output2570, pairMagnitude2542]

def corrSharedN02701MinusP015Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP015Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP015Output2570.1‖ ≤ (corrSharedN02701MinusP015Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP015BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP015Output2570,
    kernelN02701MinusP015Center2555, kernelN02701MinusP015Error2555, embedPair2542]

theorem corrSharedN02701MinusP015Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP015Output2570.1) + embedPair2542
            corrSharedN02701MinusP015Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP015Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP015Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP015Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP015Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP015Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP015Output2570, pairMagnitude2542]

def corrSharedN02701MinusP016Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP016Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP016Output2570.1‖ ≤ (corrSharedN02701MinusP016Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP016BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP016Output2570,
    kernelN02701MinusP016Center2555, kernelN02701MinusP016Error2555, embedPair2542]

theorem corrSharedN02701MinusP016Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP016Output2570.1) + embedPair2542
            corrSharedN02701MinusP016Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP016Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP016Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP016Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP016Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP016Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP016Output2570, pairMagnitude2542]

def corrSharedN02701MinusP017Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP017Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP017Output2570.1‖ ≤ (corrSharedN02701MinusP017Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP017BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP017Output2570,
    kernelN02701MinusP017Center2555, kernelN02701MinusP017Error2555, embedPair2542]

theorem corrSharedN02701MinusP017Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP017Output2570.1) + embedPair2542
            corrSharedN02701MinusP017Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP017Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP017Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP017Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP017Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP017Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP017Output2570, pairMagnitude2542]

def corrSharedN02701MinusP018Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP018Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP018Output2570.1‖ ≤ (corrSharedN02701MinusP018Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP018BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP018Output2570,
    kernelN02701MinusP018Center2555, kernelN02701MinusP018Error2555, embedPair2542]

theorem corrSharedN02701MinusP018Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP018Output2570.1) + embedPair2542
            corrSharedN02701MinusP018Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP018Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP018Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP018Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP018Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP018Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP018Output2570, pairMagnitude2542]

def corrSharedN02701MinusP019Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP019Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP019Output2570.1‖ ≤ (corrSharedN02701MinusP019Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP019BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP019Output2570,
    kernelN02701MinusP019Center2555, kernelN02701MinusP019Error2555, embedPair2542]

theorem corrSharedN02701MinusP019Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP019Output2570.1) + embedPair2542
            corrSharedN02701MinusP019Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP019Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP019Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP019Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP019Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP019Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP019Output2570, pairMagnitude2542]

def corrSharedN02701MinusP020Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP020Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP020Output2570.1‖ ≤ (corrSharedN02701MinusP020Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP020BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP020Output2570,
    kernelN02701MinusP020Center2555, kernelN02701MinusP020Error2555, embedPair2542]

theorem corrSharedN02701MinusP020Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP020Output2570.1) + embedPair2542
            corrSharedN02701MinusP020Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP020Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP020Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP020Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP020Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP020Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP020Output2570, pairMagnitude2542]

def corrSharedN02701MinusP021Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP021Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP021Output2570.1‖ ≤ (corrSharedN02701MinusP021Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP021BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP021Output2570,
    kernelN02701MinusP021Center2555, kernelN02701MinusP021Error2555, embedPair2542]

theorem corrSharedN02701MinusP021Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP021Output2570.1) + embedPair2542
            corrSharedN02701MinusP021Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP021Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP021Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP021Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP021Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP021Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP021Output2570, pairMagnitude2542]

def corrSharedN02701MinusP022Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP022Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP022Output2570.1‖ ≤ (corrSharedN02701MinusP022Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP022BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP022Output2570,
    kernelN02701MinusP022Center2555, kernelN02701MinusP022Error2555, embedPair2542]

theorem corrSharedN02701MinusP022Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP022Output2570.1) + embedPair2542
            corrSharedN02701MinusP022Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP022Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP022Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP022Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP022Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP022Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP022Output2570, pairMagnitude2542]

def corrSharedN02701MinusP023Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP023Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP023Output2570.1‖ ≤ (corrSharedN02701MinusP023Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP023BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP023Output2570,
    kernelN02701MinusP023Center2555, kernelN02701MinusP023Error2555, embedPair2542]

theorem corrSharedN02701MinusP023Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP023Output2570.1) + embedPair2542
            corrSharedN02701MinusP023Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP023Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP023Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP023Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP023Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP023Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP023Output2570, pairMagnitude2542]

def corrSharedN02701MinusP024Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP024Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP024Output2570.1‖ ≤ (corrSharedN02701MinusP024Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP024BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP024Output2570,
    kernelN02701MinusP024Center2555, kernelN02701MinusP024Error2555, embedPair2542]

theorem corrSharedN02701MinusP024Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP024Output2570.1) + embedPair2542
            corrSharedN02701MinusP024Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP024Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP024Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP024Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP024Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP024Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP024Output2570, pairMagnitude2542]

def corrSharedN02701MinusP025Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP025Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP025Output2570.1‖ ≤ (corrSharedN02701MinusP025Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP025BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP025Output2570,
    kernelN02701MinusP025Center2555, kernelN02701MinusP025Error2555, embedPair2542]

theorem corrSharedN02701MinusP025Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP025Output2570.1) + embedPair2542
            corrSharedN02701MinusP025Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP025Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP025Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP025Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP025Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP025Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP025Output2570, pairMagnitude2542]

def corrSharedN02701MinusP026Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP026Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP026Output2570.1‖ ≤ (corrSharedN02701MinusP026Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP026BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP026Output2570,
    kernelN02701MinusP026Center2555, kernelN02701MinusP026Error2555, embedPair2542]

theorem corrSharedN02701MinusP026Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP026Output2570.1) + embedPair2542
            corrSharedN02701MinusP026Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP026Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP026Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP026Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP026Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP026Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP026Output2570, pairMagnitude2542]

def corrSharedN02701MinusP027Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP027Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP027Output2570.1‖ ≤ (corrSharedN02701MinusP027Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP027BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP027Output2570,
    kernelN02701MinusP027Center2555, kernelN02701MinusP027Error2555, embedPair2542]

theorem corrSharedN02701MinusP027Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP027Output2570.1) + embedPair2542
            corrSharedN02701MinusP027Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP027Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP027Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP027Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP027Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP027Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP027Output2570, pairMagnitude2542]

def corrSharedN02701MinusP028Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP028Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP028Output2570.1‖ ≤ (corrSharedN02701MinusP028Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP028BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP028Output2570,
    kernelN02701MinusP028Center2555, kernelN02701MinusP028Error2555, embedPair2542]

theorem corrSharedN02701MinusP028Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP028Output2570.1) + embedPair2542
            corrSharedN02701MinusP028Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP028Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP028Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP028Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP028Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP028Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP028Output2570, pairMagnitude2542]

def corrSharedN02701MinusP029Output2570 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02701MinusP029Error2570 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP029Output2570.1‖ ≤ (corrSharedN02701MinusP029Output2570.2 : ℝ)
                := by
  have h := kernelN02701MinusP029BaseError2555
  convert h using 1
  all_goals norm_num [corrSharedN02701MinusPosition2570, kernelN02701MinusPosition2555,
      corrSharedN02701MinusP029Output2570,
    kernelN02701MinusP029Center2555, kernelN02701MinusP029Error2555, embedPair2542]

theorem corrSharedN02701MinusP029Norm2570 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02701MinusPosition2570‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP029Output2570.1) + embedPair2542
            corrSharedN02701MinusP029Output2570.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02701MinusPosition2570 - embedPair2542
            corrSharedN02701MinusP029Output2570.1‖ + ‖embedPair2542
            corrSharedN02701MinusP029Output2570.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02701MinusP029Output2570.2 : ℝ) + (pairMagnitude2542
        corrSharedN02701MinusP029Output2570.1 : ℝ) :=
      add_le_add corrSharedN02701MinusP029Error2570 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02701MinusP029Output2570, pairMagnitude2542]

noncomputable def corrSharedN02701MinusValue2570 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 corrSharedN02701MinusP000Output2570.1
  | 1 => embedPair2542 corrSharedN02701MinusP001Output2570.1
  | 2 => embedPair2542 corrSharedN02701MinusP002Output2570.1
  | 3 => embedPair2542 corrSharedN02701MinusP003Output2570.1
  | 4 => embedPair2542 corrSharedN02701MinusP004Output2570.1
  | 5 => embedPair2542 corrSharedN02701MinusP005Output2570.1
  | 6 => embedPair2542 corrSharedN02701MinusP006Output2570.1
  | 7 => embedPair2542 corrSharedN02701MinusP007Output2570.1
  | 8 => embedPair2542 corrSharedN02701MinusP008Output2570.1
  | 9 => embedPair2542 corrSharedN02701MinusP009Output2570.1
  | 10 => embedPair2542 corrSharedN02701MinusP010Output2570.1
  | 11 => embedPair2542 corrSharedN02701MinusP011Output2570.1
  | 12 => embedPair2542 corrSharedN02701MinusP012Output2570.1
  | 13 => embedPair2542 corrSharedN02701MinusP013Output2570.1
  | 14 => embedPair2542 corrSharedN02701MinusP014Output2570.1
  | 15 => embedPair2542 corrSharedN02701MinusP015Output2570.1
  | 16 => embedPair2542 corrSharedN02701MinusP016Output2570.1
  | 17 => embedPair2542 corrSharedN02701MinusP017Output2570.1
  | 18 => embedPair2542 corrSharedN02701MinusP018Output2570.1
  | 19 => embedPair2542 corrSharedN02701MinusP019Output2570.1
  | 20 => embedPair2542 corrSharedN02701MinusP020Output2570.1
  | 21 => embedPair2542 corrSharedN02701MinusP021Output2570.1
  | 22 => embedPair2542 corrSharedN02701MinusP022Output2570.1
  | 23 => embedPair2542 corrSharedN02701MinusP023Output2570.1
  | 24 => embedPair2542 corrSharedN02701MinusP024Output2570.1
  | 25 => embedPair2542 corrSharedN02701MinusP025Output2570.1
  | 26 => embedPair2542 corrSharedN02701MinusP026Output2570.1
  | 27 => embedPair2542 corrSharedN02701MinusP027Output2570.1
  | 28 => embedPair2542 corrSharedN02701MinusP028Output2570.1
  | 29 => embedPair2542 corrSharedN02701MinusP029Output2570.1
  | _ => 0

noncomputable def corrSharedN02701MinusError2570 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (corrSharedN02701MinusP000Output2570.2 : ℝ)
  | 1 => (corrSharedN02701MinusP001Output2570.2 : ℝ)
  | 2 => (corrSharedN02701MinusP002Output2570.2 : ℝ)
  | 3 => (corrSharedN02701MinusP003Output2570.2 : ℝ)
  | 4 => (corrSharedN02701MinusP004Output2570.2 : ℝ)
  | 5 => (corrSharedN02701MinusP005Output2570.2 : ℝ)
  | 6 => (corrSharedN02701MinusP006Output2570.2 : ℝ)
  | 7 => (corrSharedN02701MinusP007Output2570.2 : ℝ)
  | 8 => (corrSharedN02701MinusP008Output2570.2 : ℝ)
  | 9 => (corrSharedN02701MinusP009Output2570.2 : ℝ)
  | 10 => (corrSharedN02701MinusP010Output2570.2 : ℝ)
  | 11 => (corrSharedN02701MinusP011Output2570.2 : ℝ)
  | 12 => (corrSharedN02701MinusP012Output2570.2 : ℝ)
  | 13 => (corrSharedN02701MinusP013Output2570.2 : ℝ)
  | 14 => (corrSharedN02701MinusP014Output2570.2 : ℝ)
  | 15 => (corrSharedN02701MinusP015Output2570.2 : ℝ)
  | 16 => (corrSharedN02701MinusP016Output2570.2 : ℝ)
  | 17 => (corrSharedN02701MinusP017Output2570.2 : ℝ)
  | 18 => (corrSharedN02701MinusP018Output2570.2 : ℝ)
  | 19 => (corrSharedN02701MinusP019Output2570.2 : ℝ)
  | 20 => (corrSharedN02701MinusP020Output2570.2 : ℝ)
  | 21 => (corrSharedN02701MinusP021Output2570.2 : ℝ)
  | 22 => (corrSharedN02701MinusP022Output2570.2 : ℝ)
  | 23 => (corrSharedN02701MinusP023Output2570.2 : ℝ)
  | 24 => (corrSharedN02701MinusP024Output2570.2 : ℝ)
  | 25 => (corrSharedN02701MinusP025Output2570.2 : ℝ)
  | 26 => (corrSharedN02701MinusP026Output2570.2 : ℝ)
  | 27 => (corrSharedN02701MinusP027Output2570.2 : ℝ)
  | 28 => (corrSharedN02701MinusP028Output2570.2 : ℝ)
  | 29 => (corrSharedN02701MinusP029Output2570.2 : ℝ)
  | _ => 0

theorem corrSharedN02701MinusExp_error2570 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02701MinusPosition2570 -
            corrSharedN02701MinusValue2570 i‖
            ≤ corrSharedN02701MinusError2570 i := by
  fin_cases i
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP000Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP001Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP002Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP003Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP004Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP005Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP006Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP007Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP008Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP009Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP010Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP011Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP012Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP013Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP014Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP015Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP016Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP017Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP018Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP019Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP020Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP021Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP022Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP023Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP024Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP025Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP026Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP027Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP028Error2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP029Error2570

theorem corrSharedN02701MinusUnit_norm2570 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02701MinusPosition2570‖ ≤ 1 := by
  fin_cases i
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP000Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP001Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP002Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP003Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP004Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP005Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP006Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP007Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP008Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP009Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP010Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP011Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP012Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP013Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP014Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP015Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP016Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP017Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP018Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP019Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP020Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP021Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP022Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP023Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP024Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP025Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP026Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP027Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP028Norm2570
  · simpa only [corrSharedN02701MinusValue2570, corrSharedN02701MinusError2570] using
      corrSharedN02701MinusP029Norm2570

noncomputable def corrSharedN02701MinusSumValue2570 : ℂ := ⟨(((((9589699664762808549629740779 *
    10^40
        + 5368021363168948678852689159340610259667) * 10^40
        + 9312965134531054211330445593092588392024) * 10^40
        + 8132618430304520795695542621976481019015) : ℝ) /
        (((818347651974035467503297424206 * 10^40
        + 8997880541605115107661973708228420240334) * 10^40
        + 4910116863872081752308147603928772167103) * 10^40
        + 1890017752304314136471348263332131897344)),
    (((-(((2061823169060145041419078410 * 10^40
        + 7953545456509015117818604186078088674185) * 10^40
        + 3235030531932302355248830553388074248569) * 10^40
        + 9082661431210980560739410185786542013189)) : ℝ) /
        (((204586912993508866875824356051 * 10^40
        + 7249470135401278776915493427057105060083) * 10^40
        + 6227529215968020438077036900982193041775) * 10^40
        + 7972504438076078534117837065833032974336))⟩

noncomputable def corrSharedN02701MinusUpper2570 : ℝ := ((77279669 : ℝ) /
        5000000000)

theorem corrSharedN02701MinusSum_eq2570 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02701MinusValue2570 i) =
      corrSharedN02701MinusSumValue2570 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        corrSharedN02701MinusValue2570,
      corrSharedN02701MinusSumValue2570, embedPair2542, corrSharedN02701MinusP000Output2570,
      corrSharedN02701MinusP001Output2570,
      corrSharedN02701MinusP002Output2570,
      corrSharedN02701MinusP003Output2570,
      corrSharedN02701MinusP004Output2570,
      corrSharedN02701MinusP005Output2570,
      corrSharedN02701MinusP006Output2570,
      corrSharedN02701MinusP007Output2570,
      corrSharedN02701MinusP008Output2570,
      corrSharedN02701MinusP009Output2570,
      corrSharedN02701MinusP010Output2570,
      corrSharedN02701MinusP011Output2570,
      corrSharedN02701MinusP012Output2570,
      corrSharedN02701MinusP013Output2570,
      corrSharedN02701MinusP014Output2570,
      corrSharedN02701MinusP015Output2570,
      corrSharedN02701MinusP016Output2570,
      corrSharedN02701MinusP017Output2570,
      corrSharedN02701MinusP018Output2570,
      corrSharedN02701MinusP019Output2570,
      corrSharedN02701MinusP020Output2570,
      corrSharedN02701MinusP021Output2570,
      corrSharedN02701MinusP022Output2570,
      corrSharedN02701MinusP023Output2570,
      corrSharedN02701MinusP024Output2570,
      corrSharedN02701MinusP025Output2570,
      corrSharedN02701MinusP026Output2570,
      corrSharedN02701MinusP027Output2570,
      corrSharedN02701MinusP028Output2570,
      corrSharedN02701MinusP029Output2570, Complex.mul_re, Complex.mul_im]

theorem corrSharedN02701MinusSum_norm2570 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02701MinusValue2570 i‖ ≤
      ((154559337 : ℝ) /
        10000000000) := by
  rw [corrSharedN02701MinusSum_eq2570]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [corrSharedN02701MinusSumValue2570]

theorem corrSharedN02701MinusEvaluation_charge2570 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * corrSharedN02701MinusError2570 i) ≤ (1 :
          ℝ)/10^12
          := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      corrSharedN02701MinusError2570,
      corrSharedN02701MinusP000Output2570,
      corrSharedN02701MinusP001Output2570,
      corrSharedN02701MinusP002Output2570,
      corrSharedN02701MinusP003Output2570,
      corrSharedN02701MinusP004Output2570,
      corrSharedN02701MinusP005Output2570,
      corrSharedN02701MinusP006Output2570,
      corrSharedN02701MinusP007Output2570,
      corrSharedN02701MinusP008Output2570,
      corrSharedN02701MinusP009Output2570,
      corrSharedN02701MinusP010Output2570,
      corrSharedN02701MinusP011Output2570,
      corrSharedN02701MinusP012Output2570,
      corrSharedN02701MinusP013Output2570,
      corrSharedN02701MinusP014Output2570,
      corrSharedN02701MinusP015Output2570,
      corrSharedN02701MinusP016Output2570,
      corrSharedN02701MinusP017Output2570,
      corrSharedN02701MinusP018Output2570,
      corrSharedN02701MinusP019Output2570,
      corrSharedN02701MinusP020Output2570,
      corrSharedN02701MinusP021Output2570,
      corrSharedN02701MinusP022Output2570,
      corrSharedN02701MinusP023Output2570,
      corrSharedN02701MinusP024Output2570,
      corrSharedN02701MinusP025Output2570,
      corrSharedN02701MinusP026Output2570,
      corrSharedN02701MinusP027Output2570,
      corrSharedN02701MinusP028Output2570,
      corrSharedN02701MinusP029Output2570]

theorem corrSharedN02701MinusSigned_le2570 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 corrSharedN02701MinusPosition2570 ≤ corrSharedN02701MinusUpper2570 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02701MinusPosition2570‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02701MinusValue2570 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * corrSharedN02701MinusError2570 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (corrSharedN02701MinusExp_error2570 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02701MinusPosition2570‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (corrSharedN02701MinusUnit_norm2570 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02701MinusPosition2570‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 corrSharedN02701MinusUpper2570
  linarith [corrSharedN02701MinusSum_norm2570, corrSharedN02701MinusEvaluation_charge2570]

theorem corrSharedN02701MinusPhysical_le2570 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 corrSharedN02701MinusPosition2570‖ ≤
      corrSharedN02701MinusUpper2570 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        corrSharedN02701MinusPosition2570
  simpa only [iteratedDeriv_zero] using h.trans corrSharedN02701MinusSigned_le2570

theorem corrSharedN02701MinusGrid2570 :
    -stripRadius2303 + (2701 : ℝ)*(2*stripRadius2303/10240) = corrSharedN02701MinusPosition2570 :=
        by
  norm_num [stripRadius2303, corrSharedN02701MinusPosition2570]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrSharedN02701MinusSigned_le2570
#print axioms ConnesWeilRH.Dev.corrSharedN02701MinusPhysical_le2570
