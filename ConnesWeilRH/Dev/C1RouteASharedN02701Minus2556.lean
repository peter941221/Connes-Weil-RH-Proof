import ConnesWeilRH.Dev.C1RouteAKernelN02701Minus2555
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def sharedN02701MinusPosition2556 : ℝ := (((-158531586419) : ℝ) /
        51200000000)

def sharedN02701MinusP000Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02701MinusP000Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP000Output2556.1‖ ≤ (sharedN02701MinusP000Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP000BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP000Output2556,
    kernelN02701MinusP000Center2555, kernelN02701MinusP000Error2555, embedPair2542]

theorem sharedN02701MinusP000Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP000Output2556.1) + embedPair2542
            sharedN02701MinusP000Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP000Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP000Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP000Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP000Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP000Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP000Output2556, pairMagnitude2542]

def sharedN02701MinusP001Output2556 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP001Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP001Output2556.1‖ ≤ (sharedN02701MinusP001Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP001BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP001Output2556,
    kernelN02701MinusP001Center2555, kernelN02701MinusP001Error2555, embedPair2542]

theorem sharedN02701MinusP001Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP001Output2556.1) + embedPair2542
            sharedN02701MinusP001Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP001Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP001Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP001Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP001Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP001Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP001Output2556, pairMagnitude2542]

def sharedN02701MinusP002Output2556 : RatState2542 :=
  (((((-7432742102829368094385) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-11177578774756275941739) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((49382499124458385033 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP002Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP002Output2556.1‖ ≤ (sharedN02701MinusP002Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP002BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP002Output2556,
    kernelN02701MinusP002Center2555, kernelN02701MinusP002Error2555, embedPair2542]

theorem sharedN02701MinusP002Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP002Output2556.1) + embedPair2542
            sharedN02701MinusP002Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP002Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP002Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP002Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP002Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP002Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP002Output2556, pairMagnitude2542]

def sharedN02701MinusP003Output2556 : RatState2542 :=
  (((((-128031342998015805707829314715) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-192537343849641036358254016761) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((797028780675931752600253645 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP003Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP003Output2556.1‖ ≤ (sharedN02701MinusP003Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP003BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP003Output2556,
    kernelN02701MinusP003Center2555, kernelN02701MinusP003Error2555, embedPair2542]

theorem sharedN02701MinusP003Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP003Output2556.1) + embedPair2542
            sharedN02701MinusP003Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP003Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP003Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP003Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP003Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP003Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP003Output2556, pairMagnitude2542]

def sharedN02701MinusP004Output2556 : RatState2542 :=
  (((((-64207546511769766768481979511471) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((96557219279266825819155349428839 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((97529468585144800089090291783 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem sharedN02701MinusP004Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP004Output2556.1‖ ≤ (sharedN02701MinusP004Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP004BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP004Output2556,
    kernelN02701MinusP004Center2555, kernelN02701MinusP004Error2555, embedPair2542]

theorem sharedN02701MinusP004Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP004Output2556.1) + embedPair2542
            sharedN02701MinusP004Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP004Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP004Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP004Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP004Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP004Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP004Output2556, pairMagnitude2542]

def sharedN02701MinusP005Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02701MinusP005Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP005Output2556.1‖ ≤ (sharedN02701MinusP005Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP005BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP005Output2556,
    kernelN02701MinusP005Center2555, kernelN02701MinusP005Error2555, embedPair2542]

theorem sharedN02701MinusP005Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP005Output2556.1) + embedPair2542
            sharedN02701MinusP005Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP005Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP005Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP005Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP005Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP005Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP005Output2556, pairMagnitude2542]

def sharedN02701MinusP006Output2556 : RatState2542 :=
  ((((21384329496406693 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((3767500786445 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN02701MinusP006Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP006Output2556.1‖ ≤ (sharedN02701MinusP006Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP006BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP006Output2556,
    kernelN02701MinusP006Center2555, kernelN02701MinusP006Error2555, embedPair2542]

theorem sharedN02701MinusP006Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP006Output2556.1) + embedPair2542
            sharedN02701MinusP006Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP006Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP006Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP006Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP006Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP006Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP006Output2556, pairMagnitude2542]

def sharedN02701MinusP007Output2556 : RatState2542 :=
  ((((231219924674649256075727664923 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((16000632657409328590635391 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN02701MinusP007Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP007Output2556.1‖ ≤ (sharedN02701MinusP007Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP007BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP007Output2556,
    kernelN02701MinusP007Center2555, kernelN02701MinusP007Error2555, embedPair2542]

theorem sharedN02701MinusP007Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP007Output2556.1) + embedPair2542
            sharedN02701MinusP007Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP007Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP007Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP007Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP007Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP007Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP007Output2556, pairMagnitude2542]

def sharedN02701MinusP008Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP008Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP008Output2556.1‖ ≤ (sharedN02701MinusP008Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP008BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP008Output2556,
    kernelN02701MinusP008Center2555, kernelN02701MinusP008Error2555, embedPair2542]

theorem sharedN02701MinusP008Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP008Output2556.1) + embedPair2542
            sharedN02701MinusP008Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP008Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP008Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP008Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP008Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP008Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP008Output2556, pairMagnitude2542]

def sharedN02701MinusP009Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP009Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP009Output2556.1‖ ≤ (sharedN02701MinusP009Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP009BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP009Output2556,
    kernelN02701MinusP009Center2555, kernelN02701MinusP009Error2555, embedPair2542]

theorem sharedN02701MinusP009Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP009Output2556.1) + embedPair2542
            sharedN02701MinusP009Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP009Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP009Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP009Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP009Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP009Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP009Output2556, pairMagnitude2542]

def sharedN02701MinusP010Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP010Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP010Output2556.1‖ ≤ (sharedN02701MinusP010Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP010BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP010Output2556,
    kernelN02701MinusP010Center2555, kernelN02701MinusP010Error2555, embedPair2542]

theorem sharedN02701MinusP010Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP010Output2556.1) + embedPair2542
            sharedN02701MinusP010Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP010Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP010Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP010Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP010Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP010Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP010Output2556, pairMagnitude2542]

def sharedN02701MinusP011Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP011Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP011Output2556.1‖ ≤ (sharedN02701MinusP011Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP011BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP011Output2556,
    kernelN02701MinusP011Center2555, kernelN02701MinusP011Error2555, embedPair2542]

theorem sharedN02701MinusP011Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP011Output2556.1) + embedPair2542
            sharedN02701MinusP011Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP011Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP011Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP011Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP011Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP011Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP011Output2556, pairMagnitude2542]

def sharedN02701MinusP012Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP012Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP012Output2556.1‖ ≤ (sharedN02701MinusP012Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP012BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP012Output2556,
    kernelN02701MinusP012Center2555, kernelN02701MinusP012Error2555, embedPair2542]

theorem sharedN02701MinusP012Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP012Output2556.1) + embedPair2542
            sharedN02701MinusP012Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP012Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP012Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP012Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP012Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP012Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP012Output2556, pairMagnitude2542]

def sharedN02701MinusP013Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP013Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP013Output2556.1‖ ≤ (sharedN02701MinusP013Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP013BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP013Output2556,
    kernelN02701MinusP013Center2555, kernelN02701MinusP013Error2555, embedPair2542]

theorem sharedN02701MinusP013Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP013Output2556.1) + embedPair2542
            sharedN02701MinusP013Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP013Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP013Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP013Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP013Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP013Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP013Output2556, pairMagnitude2542]

def sharedN02701MinusP014Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP014Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP014Output2556.1‖ ≤ (sharedN02701MinusP014Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP014BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP014Output2556,
    kernelN02701MinusP014Center2555, kernelN02701MinusP014Error2555, embedPair2542]

theorem sharedN02701MinusP014Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP014Output2556.1) + embedPair2542
            sharedN02701MinusP014Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP014Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP014Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP014Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP014Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP014Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP014Output2556, pairMagnitude2542]

def sharedN02701MinusP015Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP015Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP015Output2556.1‖ ≤ (sharedN02701MinusP015Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP015BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP015Output2556,
    kernelN02701MinusP015Center2555, kernelN02701MinusP015Error2555, embedPair2542]

theorem sharedN02701MinusP015Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP015Output2556.1) + embedPair2542
            sharedN02701MinusP015Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP015Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP015Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP015Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP015Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP015Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP015Output2556, pairMagnitude2542]

def sharedN02701MinusP016Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP016Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP016Output2556.1‖ ≤ (sharedN02701MinusP016Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP016BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP016Output2556,
    kernelN02701MinusP016Center2555, kernelN02701MinusP016Error2555, embedPair2542]

theorem sharedN02701MinusP016Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP016Output2556.1) + embedPair2542
            sharedN02701MinusP016Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP016Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP016Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP016Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP016Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP016Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP016Output2556, pairMagnitude2542]

def sharedN02701MinusP017Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP017Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP017Output2556.1‖ ≤ (sharedN02701MinusP017Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP017BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP017Output2556,
    kernelN02701MinusP017Center2555, kernelN02701MinusP017Error2555, embedPair2542]

theorem sharedN02701MinusP017Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP017Output2556.1) + embedPair2542
            sharedN02701MinusP017Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP017Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP017Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP017Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP017Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP017Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP017Output2556, pairMagnitude2542]

def sharedN02701MinusP018Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP018Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP018Output2556.1‖ ≤ (sharedN02701MinusP018Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP018BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP018Output2556,
    kernelN02701MinusP018Center2555, kernelN02701MinusP018Error2555, embedPair2542]

theorem sharedN02701MinusP018Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP018Output2556.1) + embedPair2542
            sharedN02701MinusP018Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP018Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP018Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP018Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP018Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP018Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP018Output2556, pairMagnitude2542]

def sharedN02701MinusP019Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP019Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP019Output2556.1‖ ≤ (sharedN02701MinusP019Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP019BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP019Output2556,
    kernelN02701MinusP019Center2555, kernelN02701MinusP019Error2555, embedPair2542]

theorem sharedN02701MinusP019Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP019Output2556.1) + embedPair2542
            sharedN02701MinusP019Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP019Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP019Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP019Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP019Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP019Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP019Output2556, pairMagnitude2542]

def sharedN02701MinusP020Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP020Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP020Output2556.1‖ ≤ (sharedN02701MinusP020Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP020BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP020Output2556,
    kernelN02701MinusP020Center2555, kernelN02701MinusP020Error2555, embedPair2542]

theorem sharedN02701MinusP020Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP020Output2556.1) + embedPair2542
            sharedN02701MinusP020Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP020Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP020Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP020Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP020Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP020Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP020Output2556, pairMagnitude2542]

def sharedN02701MinusP021Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP021Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP021Output2556.1‖ ≤ (sharedN02701MinusP021Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP021BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP021Output2556,
    kernelN02701MinusP021Center2555, kernelN02701MinusP021Error2555, embedPair2542]

theorem sharedN02701MinusP021Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP021Output2556.1) + embedPair2542
            sharedN02701MinusP021Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP021Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP021Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP021Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP021Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP021Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP021Output2556, pairMagnitude2542]

def sharedN02701MinusP022Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP022Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP022Output2556.1‖ ≤ (sharedN02701MinusP022Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP022BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP022Output2556,
    kernelN02701MinusP022Center2555, kernelN02701MinusP022Error2555, embedPair2542]

theorem sharedN02701MinusP022Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP022Output2556.1) + embedPair2542
            sharedN02701MinusP022Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP022Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP022Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP022Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP022Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP022Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP022Output2556, pairMagnitude2542]

def sharedN02701MinusP023Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP023Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP023Output2556.1‖ ≤ (sharedN02701MinusP023Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP023BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP023Output2556,
    kernelN02701MinusP023Center2555, kernelN02701MinusP023Error2555, embedPair2542]

theorem sharedN02701MinusP023Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP023Output2556.1) + embedPair2542
            sharedN02701MinusP023Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP023Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP023Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP023Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP023Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP023Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP023Output2556, pairMagnitude2542]

def sharedN02701MinusP024Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP024Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP024Output2556.1‖ ≤ (sharedN02701MinusP024Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP024BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP024Output2556,
    kernelN02701MinusP024Center2555, kernelN02701MinusP024Error2555, embedPair2542]

theorem sharedN02701MinusP024Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP024Output2556.1) + embedPair2542
            sharedN02701MinusP024Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP024Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP024Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP024Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP024Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP024Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP024Output2556, pairMagnitude2542]

def sharedN02701MinusP025Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP025Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP025Output2556.1‖ ≤ (sharedN02701MinusP025Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP025BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP025Output2556,
    kernelN02701MinusP025Center2555, kernelN02701MinusP025Error2555, embedPair2542]

theorem sharedN02701MinusP025Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP025Output2556.1) + embedPair2542
            sharedN02701MinusP025Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP025Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP025Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP025Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP025Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP025Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP025Output2556, pairMagnitude2542]

def sharedN02701MinusP026Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP026Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP026Output2556.1‖ ≤ (sharedN02701MinusP026Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP026BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP026Output2556,
    kernelN02701MinusP026Center2555, kernelN02701MinusP026Error2555, embedPair2542]

theorem sharedN02701MinusP026Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP026Output2556.1) + embedPair2542
            sharedN02701MinusP026Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP026Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP026Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP026Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP026Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP026Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP026Output2556, pairMagnitude2542]

def sharedN02701MinusP027Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP027Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP027Output2556.1‖ ≤ (sharedN02701MinusP027Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP027BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP027Output2556,
    kernelN02701MinusP027Center2555, kernelN02701MinusP027Error2555, embedPair2542]

theorem sharedN02701MinusP027Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP027Output2556.1) + embedPair2542
            sharedN02701MinusP027Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP027Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP027Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP027Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP027Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP027Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP027Output2556, pairMagnitude2542]

def sharedN02701MinusP028Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP028Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP028Output2556.1‖ ≤ (sharedN02701MinusP028Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP028BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP028Output2556,
    kernelN02701MinusP028Center2555, kernelN02701MinusP028Error2555, embedPair2542]

theorem sharedN02701MinusP028Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP028Output2556.1) + embedPair2542
            sharedN02701MinusP028Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP028Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP028Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP028Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP028Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP028Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP028Output2556, pairMagnitude2542]

def sharedN02701MinusP029Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02701MinusP029Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP029Output2556.1‖ ≤ (sharedN02701MinusP029Output2556.2 : ℝ) := by
  have h := kernelN02701MinusP029BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02701MinusPosition2556, kernelN02701MinusPosition2555,
      sharedN02701MinusP029Output2556,
    kernelN02701MinusP029Center2555, kernelN02701MinusP029Error2555, embedPair2542]

theorem sharedN02701MinusP029Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02701MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02701MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP029Output2556.1) + embedPair2542
            sharedN02701MinusP029Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02701MinusPosition2556 - embedPair2542
            sharedN02701MinusP029Output2556.1‖ + ‖embedPair2542
            sharedN02701MinusP029Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02701MinusP029Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02701MinusP029Output2556.1 : ℝ) :=
      add_le_add sharedN02701MinusP029Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02701MinusP029Output2556, pairMagnitude2542]

noncomputable def sharedN02701MinusValue2556 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 sharedN02701MinusP000Output2556.1
  | 1 => embedPair2542 sharedN02701MinusP001Output2556.1
  | 2 => embedPair2542 sharedN02701MinusP002Output2556.1
  | 3 => embedPair2542 sharedN02701MinusP003Output2556.1
  | 4 => embedPair2542 sharedN02701MinusP004Output2556.1
  | 5 => embedPair2542 sharedN02701MinusP005Output2556.1
  | 6 => embedPair2542 sharedN02701MinusP006Output2556.1
  | 7 => embedPair2542 sharedN02701MinusP007Output2556.1
  | 8 => embedPair2542 sharedN02701MinusP008Output2556.1
  | 9 => embedPair2542 sharedN02701MinusP009Output2556.1
  | 10 => embedPair2542 sharedN02701MinusP010Output2556.1
  | 11 => embedPair2542 sharedN02701MinusP011Output2556.1
  | 12 => embedPair2542 sharedN02701MinusP012Output2556.1
  | 13 => embedPair2542 sharedN02701MinusP013Output2556.1
  | 14 => embedPair2542 sharedN02701MinusP014Output2556.1
  | 15 => embedPair2542 sharedN02701MinusP015Output2556.1
  | 16 => embedPair2542 sharedN02701MinusP016Output2556.1
  | 17 => embedPair2542 sharedN02701MinusP017Output2556.1
  | 18 => embedPair2542 sharedN02701MinusP018Output2556.1
  | 19 => embedPair2542 sharedN02701MinusP019Output2556.1
  | 20 => embedPair2542 sharedN02701MinusP020Output2556.1
  | 21 => embedPair2542 sharedN02701MinusP021Output2556.1
  | 22 => embedPair2542 sharedN02701MinusP022Output2556.1
  | 23 => embedPair2542 sharedN02701MinusP023Output2556.1
  | 24 => embedPair2542 sharedN02701MinusP024Output2556.1
  | 25 => embedPair2542 sharedN02701MinusP025Output2556.1
  | 26 => embedPair2542 sharedN02701MinusP026Output2556.1
  | 27 => embedPair2542 sharedN02701MinusP027Output2556.1
  | 28 => embedPair2542 sharedN02701MinusP028Output2556.1
  | 29 => embedPair2542 sharedN02701MinusP029Output2556.1
  | _ => 0

noncomputable def sharedN02701MinusError2556 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (sharedN02701MinusP000Output2556.2 : ℝ)
  | 1 => (sharedN02701MinusP001Output2556.2 : ℝ)
  | 2 => (sharedN02701MinusP002Output2556.2 : ℝ)
  | 3 => (sharedN02701MinusP003Output2556.2 : ℝ)
  | 4 => (sharedN02701MinusP004Output2556.2 : ℝ)
  | 5 => (sharedN02701MinusP005Output2556.2 : ℝ)
  | 6 => (sharedN02701MinusP006Output2556.2 : ℝ)
  | 7 => (sharedN02701MinusP007Output2556.2 : ℝ)
  | 8 => (sharedN02701MinusP008Output2556.2 : ℝ)
  | 9 => (sharedN02701MinusP009Output2556.2 : ℝ)
  | 10 => (sharedN02701MinusP010Output2556.2 : ℝ)
  | 11 => (sharedN02701MinusP011Output2556.2 : ℝ)
  | 12 => (sharedN02701MinusP012Output2556.2 : ℝ)
  | 13 => (sharedN02701MinusP013Output2556.2 : ℝ)
  | 14 => (sharedN02701MinusP014Output2556.2 : ℝ)
  | 15 => (sharedN02701MinusP015Output2556.2 : ℝ)
  | 16 => (sharedN02701MinusP016Output2556.2 : ℝ)
  | 17 => (sharedN02701MinusP017Output2556.2 : ℝ)
  | 18 => (sharedN02701MinusP018Output2556.2 : ℝ)
  | 19 => (sharedN02701MinusP019Output2556.2 : ℝ)
  | 20 => (sharedN02701MinusP020Output2556.2 : ℝ)
  | 21 => (sharedN02701MinusP021Output2556.2 : ℝ)
  | 22 => (sharedN02701MinusP022Output2556.2 : ℝ)
  | 23 => (sharedN02701MinusP023Output2556.2 : ℝ)
  | 24 => (sharedN02701MinusP024Output2556.2 : ℝ)
  | 25 => (sharedN02701MinusP025Output2556.2 : ℝ)
  | 26 => (sharedN02701MinusP026Output2556.2 : ℝ)
  | 27 => (sharedN02701MinusP027Output2556.2 : ℝ)
  | 28 => (sharedN02701MinusP028Output2556.2 : ℝ)
  | 29 => (sharedN02701MinusP029Output2556.2 : ℝ)
  | _ => 0

theorem sharedN02701MinusExp_error2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN02701MinusPosition2556 - sharedN02701MinusValue2556 i‖
            ≤ sharedN02701MinusError2556 i := by
  fin_cases i
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP000Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP001Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP002Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP003Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP004Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP005Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP006Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP007Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP008Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP009Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP010Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP011Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP012Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP013Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP014Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP015Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP016Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP017Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP018Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP019Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP020Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP021Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP022Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP023Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP024Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP025Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP026Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP027Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP028Error2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP029Error2556

theorem sharedN02701MinusUnit_norm2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN02701MinusPosition2556‖ ≤ 1 := by
  fin_cases i
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP000Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP001Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP002Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP003Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP004Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP005Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP006Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP007Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP008Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP009Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP010Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP011Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP012Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP013Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP014Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP015Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP016Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP017Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP018Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP019Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP020Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP021Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP022Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP023Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP024Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP025Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP026Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP027Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP028Norm2556
  · simpa only [sharedN02701MinusValue2556, sharedN02701MinusError2556] using
      sharedN02701MinusP029Norm2556

noncomputable def sharedN02701MinusSumValue2556 : ℂ := ⟨(((((89008395498036562458 * 10^40
        + 5337871803686228253270183368472685857175) * 10^40
        + 2238000086066445467816267353000950635943) * 10^40
        + 7036106904740780625653205793430997104213) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816)),
    (((((36664525113275142241 * 10^40
        + 4055228055970437613207943559313931799721) * 10^40
        + 1138310053850911664896702910583015893720) * 10^40
        + 3826045577130283249003245980865271554801) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816))⟩

noncomputable def sharedN02701MinusUpper2556 : ℝ := ((9637 : ℝ) /
        5000000000)

theorem sharedN02701MinusSum_eq2556 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN02701MinusValue2556 i) =
      sharedN02701MinusSumValue2556 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN02701MinusValue2556,
      sharedN02701MinusSumValue2556, embedPair2542, sharedN02701MinusP000Output2556,
      sharedN02701MinusP001Output2556,
      sharedN02701MinusP002Output2556,
      sharedN02701MinusP003Output2556,
      sharedN02701MinusP004Output2556,
      sharedN02701MinusP005Output2556,
      sharedN02701MinusP006Output2556,
      sharedN02701MinusP007Output2556,
      sharedN02701MinusP008Output2556,
      sharedN02701MinusP009Output2556,
      sharedN02701MinusP010Output2556,
      sharedN02701MinusP011Output2556,
      sharedN02701MinusP012Output2556,
      sharedN02701MinusP013Output2556,
      sharedN02701MinusP014Output2556,
      sharedN02701MinusP015Output2556,
      sharedN02701MinusP016Output2556,
      sharedN02701MinusP017Output2556,
      sharedN02701MinusP018Output2556,
      sharedN02701MinusP019Output2556,
      sharedN02701MinusP020Output2556,
      sharedN02701MinusP021Output2556,
      sharedN02701MinusP022Output2556,
      sharedN02701MinusP023Output2556,
      sharedN02701MinusP024Output2556,
      sharedN02701MinusP025Output2556,
      sharedN02701MinusP026Output2556,
      sharedN02701MinusP027Output2556,
      sharedN02701MinusP028Output2556,
      sharedN02701MinusP029Output2556, Complex.mul_re, Complex.mul_im]

theorem sharedN02701MinusSum_norm2556 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN02701MinusValue2556 i‖ ≤
      ((19273 : ℝ) /
        10000000000) := by
  rw [sharedN02701MinusSum_eq2556]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [sharedN02701MinusSumValue2556]

theorem sharedN02701MinusEvaluation_charge2556 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * sharedN02701MinusError2556 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN02701MinusError2556,
      sharedN02701MinusP000Output2556,
      sharedN02701MinusP001Output2556,
      sharedN02701MinusP002Output2556,
      sharedN02701MinusP003Output2556,
      sharedN02701MinusP004Output2556,
      sharedN02701MinusP005Output2556,
      sharedN02701MinusP006Output2556,
      sharedN02701MinusP007Output2556,
      sharedN02701MinusP008Output2556,
      sharedN02701MinusP009Output2556,
      sharedN02701MinusP010Output2556,
      sharedN02701MinusP011Output2556,
      sharedN02701MinusP012Output2556,
      sharedN02701MinusP013Output2556,
      sharedN02701MinusP014Output2556,
      sharedN02701MinusP015Output2556,
      sharedN02701MinusP016Output2556,
      sharedN02701MinusP017Output2556,
      sharedN02701MinusP018Output2556,
      sharedN02701MinusP019Output2556,
      sharedN02701MinusP020Output2556,
      sharedN02701MinusP021Output2556,
      sharedN02701MinusP022Output2556,
      sharedN02701MinusP023Output2556,
      sharedN02701MinusP024Output2556,
      sharedN02701MinusP025Output2556,
      sharedN02701MinusP026Output2556,
      sharedN02701MinusP027Output2556,
      sharedN02701MinusP028Output2556,
      sharedN02701MinusP029Output2556]

theorem sharedN02701MinusSigned_le2556 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 sharedN02701MinusPosition2556 ≤ sharedN02701MinusUpper2556 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN02701MinusPosition2556‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN02701MinusValue2556 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * sharedN02701MinusError2556 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (sharedN02701MinusExp_error2556 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN02701MinusPosition2556‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (sharedN02701MinusUnit_norm2556 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN02701MinusPosition2556‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 sharedN02701MinusUpper2556
  linarith [sharedN02701MinusSum_norm2556, sharedN02701MinusEvaluation_charge2556]

theorem sharedN02701MinusPhysical_le2556 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 sharedN02701MinusPosition2556‖ ≤
      sharedN02701MinusUpper2556 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        sharedN02701MinusPosition2556
  simpa only [iteratedDeriv_zero] using h.trans sharedN02701MinusSigned_le2556

theorem sharedN02701MinusGrid2556 :
    -stripRadius2303 + (2701 : ℝ)*(2*stripRadius2303/10240) = sharedN02701MinusPosition2556 :=
        by
  norm_num [stripRadius2303, sharedN02701MinusPosition2556]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.sharedN02701MinusSigned_le2556
#print axioms ConnesWeilRH.Dev.sharedN02701MinusPhysical_le2556
