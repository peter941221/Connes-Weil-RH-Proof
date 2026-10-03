import ConnesWeilRH.Dev.C1RouteAKernelN02700Minus2555
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def sharedN02700MinusPosition2556 : ℝ := (((-7929856121) : ℝ) /
        2560000000)

def sharedN02700MinusP000Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP000Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP000Output2556.1‖ ≤ (sharedN02700MinusP000Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP000BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP000Output2556,
    kernelN02700MinusP000Center2555, kernelN02700MinusP000Error2555, embedPair2542]

theorem sharedN02700MinusP000Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP000Output2556.1) + embedPair2542
            sharedN02700MinusP000Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP000Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP000Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP000Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP000Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP000Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP000Output2556, pairMagnitude2542]

def sharedN02700MinusP001Output2556 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02700MinusP001Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP001Output2556.1‖ ≤ (sharedN02700MinusP001Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP001BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP001Output2556,
    kernelN02700MinusP001Center2555, kernelN02700MinusP001Error2555, embedPair2542]

theorem sharedN02700MinusP001Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP001Output2556.1) + embedPair2542
            sharedN02700MinusP001Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP001Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP001Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP001Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP001Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP001Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP001Output2556, pairMagnitude2542]

def sharedN02700MinusP002Output2556 : RatState2542 :=
  (((((-236687586501322481317) : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    (((-10235158114556736630683) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((23242280564835055193 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem sharedN02700MinusP002Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP002Output2556.1‖ ≤ (sharedN02700MinusP002Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP002BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP002Output2556,
    kernelN02700MinusP002Center2555, kernelN02700MinusP002Error2555, embedPair2542]

theorem sharedN02700MinusP002Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP002Output2556.1) + embedPair2542
            sharedN02700MinusP002Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP002Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP002Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP002Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP002Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP002Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP002Output2556, pairMagnitude2542]

def sharedN02700MinusP003Output2556 : RatState2542 :=
  (((((-67562655288918125376430023877) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-45650528571176392534168394947) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((48559493963991329543302431 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336)))

theorem sharedN02700MinusP003Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP003Output2556.1‖ ≤ (sharedN02700MinusP003Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP003BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP003Output2556,
    kernelN02700MinusP003Center2555, kernelN02700MinusP003Error2555, embedPair2542]

theorem sharedN02700MinusP003Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP003Output2556.1) + embedPair2542
            sharedN02700MinusP003Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP003Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP003Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP003Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP003Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP003Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP003Output2556, pairMagnitude2542]

def sharedN02700MinusP004Output2556 : RatState2542 :=
  (((((-68389271845661481738864442245855) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((92418108643056889386327940952689 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((383779637246708834189989500561 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02700MinusP004Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP004Output2556.1‖ ≤ (sharedN02700MinusP004Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP004BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP004Output2556,
    kernelN02700MinusP004Center2555, kernelN02700MinusP004Error2555, embedPair2542]

theorem sharedN02700MinusP004Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP004Output2556.1) + embedPair2542
            sharedN02700MinusP004Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP004Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP004Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP004Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP004Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP004Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP004Output2556, pairMagnitude2542]

def sharedN02700MinusP005Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP005Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP005Output2556.1‖ ≤ (sharedN02700MinusP005Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP005BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP005Output2556,
    kernelN02700MinusP005Center2555, kernelN02700MinusP005Error2555, embedPair2542]

theorem sharedN02700MinusP005Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP005Output2556.1) + embedPair2542
            sharedN02700MinusP005Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP005Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP005Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP005Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP005Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP005Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP005Output2556, pairMagnitude2542]

def sharedN02700MinusP006Output2556 : RatState2542 :=
  ((((19504508082407141 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((7069434267121 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02700MinusP006Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP006Output2556.1‖ ≤ (sharedN02700MinusP006Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP006BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP006Output2556,
    kernelN02700MinusP006Center2555, kernelN02700MinusP006Error2555, embedPair2542]

theorem sharedN02700MinusP006Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP006Output2556.1) + embedPair2542
            sharedN02700MinusP006Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP006Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP006Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP006Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP006Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP006Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP006Output2556, pairMagnitude2542]

def sharedN02700MinusP007Output2556 : RatState2542 :=
  ((((227161576196330745979291438463 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((31448282402248334335030421 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem sharedN02700MinusP007Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP007Output2556.1‖ ≤ (sharedN02700MinusP007Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP007BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP007Output2556,
    kernelN02700MinusP007Center2555, kernelN02700MinusP007Error2555, embedPair2542]

theorem sharedN02700MinusP007Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP007Output2556.1) + embedPair2542
            sharedN02700MinusP007Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP007Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP007Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP007Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP007Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP007Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP007Output2556, pairMagnitude2542]

def sharedN02700MinusP008Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP008Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP008Output2556.1‖ ≤ (sharedN02700MinusP008Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP008BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP008Output2556,
    kernelN02700MinusP008Center2555, kernelN02700MinusP008Error2555, embedPair2542]

theorem sharedN02700MinusP008Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP008Output2556.1) + embedPair2542
            sharedN02700MinusP008Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP008Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP008Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP008Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP008Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP008Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP008Output2556, pairMagnitude2542]

def sharedN02700MinusP009Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP009Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP009Output2556.1‖ ≤ (sharedN02700MinusP009Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP009BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP009Output2556,
    kernelN02700MinusP009Center2555, kernelN02700MinusP009Error2555, embedPair2542]

theorem sharedN02700MinusP009Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP009Output2556.1) + embedPair2542
            sharedN02700MinusP009Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP009Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP009Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP009Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP009Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP009Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP009Output2556, pairMagnitude2542]

def sharedN02700MinusP010Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP010Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP010Output2556.1‖ ≤ (sharedN02700MinusP010Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP010BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP010Output2556,
    kernelN02700MinusP010Center2555, kernelN02700MinusP010Error2555, embedPair2542]

theorem sharedN02700MinusP010Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP010Output2556.1) + embedPair2542
            sharedN02700MinusP010Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP010Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP010Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP010Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP010Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP010Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP010Output2556, pairMagnitude2542]

def sharedN02700MinusP011Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP011Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP011Output2556.1‖ ≤ (sharedN02700MinusP011Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP011BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP011Output2556,
    kernelN02700MinusP011Center2555, kernelN02700MinusP011Error2555, embedPair2542]

theorem sharedN02700MinusP011Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP011Output2556.1) + embedPair2542
            sharedN02700MinusP011Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP011Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP011Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP011Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP011Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP011Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP011Output2556, pairMagnitude2542]

def sharedN02700MinusP012Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP012Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP012Output2556.1‖ ≤ (sharedN02700MinusP012Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP012BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP012Output2556,
    kernelN02700MinusP012Center2555, kernelN02700MinusP012Error2555, embedPair2542]

theorem sharedN02700MinusP012Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP012Output2556.1) + embedPair2542
            sharedN02700MinusP012Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP012Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP012Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP012Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP012Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP012Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP012Output2556, pairMagnitude2542]

def sharedN02700MinusP013Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP013Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP013Output2556.1‖ ≤ (sharedN02700MinusP013Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP013BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP013Output2556,
    kernelN02700MinusP013Center2555, kernelN02700MinusP013Error2555, embedPair2542]

theorem sharedN02700MinusP013Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP013Output2556.1) + embedPair2542
            sharedN02700MinusP013Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP013Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP013Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP013Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP013Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP013Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP013Output2556, pairMagnitude2542]

def sharedN02700MinusP014Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP014Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP014Output2556.1‖ ≤ (sharedN02700MinusP014Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP014BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP014Output2556,
    kernelN02700MinusP014Center2555, kernelN02700MinusP014Error2555, embedPair2542]

theorem sharedN02700MinusP014Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP014Output2556.1) + embedPair2542
            sharedN02700MinusP014Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP014Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP014Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP014Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP014Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP014Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP014Output2556, pairMagnitude2542]

def sharedN02700MinusP015Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP015Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP015Output2556.1‖ ≤ (sharedN02700MinusP015Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP015BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP015Output2556,
    kernelN02700MinusP015Center2555, kernelN02700MinusP015Error2555, embedPair2542]

theorem sharedN02700MinusP015Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP015Output2556.1) + embedPair2542
            sharedN02700MinusP015Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP015Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP015Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP015Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP015Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP015Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP015Output2556, pairMagnitude2542]

def sharedN02700MinusP016Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP016Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP016Output2556.1‖ ≤ (sharedN02700MinusP016Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP016BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP016Output2556,
    kernelN02700MinusP016Center2555, kernelN02700MinusP016Error2555, embedPair2542]

theorem sharedN02700MinusP016Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP016Output2556.1) + embedPair2542
            sharedN02700MinusP016Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP016Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP016Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP016Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP016Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP016Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP016Output2556, pairMagnitude2542]

def sharedN02700MinusP017Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP017Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP017Output2556.1‖ ≤ (sharedN02700MinusP017Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP017BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP017Output2556,
    kernelN02700MinusP017Center2555, kernelN02700MinusP017Error2555, embedPair2542]

theorem sharedN02700MinusP017Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP017Output2556.1) + embedPair2542
            sharedN02700MinusP017Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP017Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP017Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP017Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP017Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP017Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP017Output2556, pairMagnitude2542]

def sharedN02700MinusP018Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP018Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP018Output2556.1‖ ≤ (sharedN02700MinusP018Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP018BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP018Output2556,
    kernelN02700MinusP018Center2555, kernelN02700MinusP018Error2555, embedPair2542]

theorem sharedN02700MinusP018Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP018Output2556.1) + embedPair2542
            sharedN02700MinusP018Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP018Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP018Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP018Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP018Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP018Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP018Output2556, pairMagnitude2542]

def sharedN02700MinusP019Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP019Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP019Output2556.1‖ ≤ (sharedN02700MinusP019Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP019BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP019Output2556,
    kernelN02700MinusP019Center2555, kernelN02700MinusP019Error2555, embedPair2542]

theorem sharedN02700MinusP019Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP019Output2556.1) + embedPair2542
            sharedN02700MinusP019Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP019Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP019Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP019Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP019Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP019Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP019Output2556, pairMagnitude2542]

def sharedN02700MinusP020Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP020Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP020Output2556.1‖ ≤ (sharedN02700MinusP020Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP020BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP020Output2556,
    kernelN02700MinusP020Center2555, kernelN02700MinusP020Error2555, embedPair2542]

theorem sharedN02700MinusP020Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP020Output2556.1) + embedPair2542
            sharedN02700MinusP020Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP020Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP020Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP020Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP020Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP020Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP020Output2556, pairMagnitude2542]

def sharedN02700MinusP021Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP021Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP021Output2556.1‖ ≤ (sharedN02700MinusP021Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP021BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP021Output2556,
    kernelN02700MinusP021Center2555, kernelN02700MinusP021Error2555, embedPair2542]

theorem sharedN02700MinusP021Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP021Output2556.1) + embedPair2542
            sharedN02700MinusP021Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP021Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP021Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP021Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP021Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP021Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP021Output2556, pairMagnitude2542]

def sharedN02700MinusP022Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP022Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP022Output2556.1‖ ≤ (sharedN02700MinusP022Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP022BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP022Output2556,
    kernelN02700MinusP022Center2555, kernelN02700MinusP022Error2555, embedPair2542]

theorem sharedN02700MinusP022Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP022Output2556.1) + embedPair2542
            sharedN02700MinusP022Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP022Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP022Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP022Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP022Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP022Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP022Output2556, pairMagnitude2542]

def sharedN02700MinusP023Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP023Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP023Output2556.1‖ ≤ (sharedN02700MinusP023Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP023BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP023Output2556,
    kernelN02700MinusP023Center2555, kernelN02700MinusP023Error2555, embedPair2542]

theorem sharedN02700MinusP023Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP023Output2556.1) + embedPair2542
            sharedN02700MinusP023Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP023Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP023Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP023Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP023Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP023Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP023Output2556, pairMagnitude2542]

def sharedN02700MinusP024Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP024Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP024Output2556.1‖ ≤ (sharedN02700MinusP024Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP024BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP024Output2556,
    kernelN02700MinusP024Center2555, kernelN02700MinusP024Error2555, embedPair2542]

theorem sharedN02700MinusP024Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP024Output2556.1) + embedPair2542
            sharedN02700MinusP024Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP024Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP024Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP024Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP024Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP024Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP024Output2556, pairMagnitude2542]

def sharedN02700MinusP025Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP025Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP025Output2556.1‖ ≤ (sharedN02700MinusP025Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP025BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP025Output2556,
    kernelN02700MinusP025Center2555, kernelN02700MinusP025Error2555, embedPair2542]

theorem sharedN02700MinusP025Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP025Output2556.1) + embedPair2542
            sharedN02700MinusP025Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP025Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP025Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP025Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP025Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP025Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP025Output2556, pairMagnitude2542]

def sharedN02700MinusP026Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP026Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP026Output2556.1‖ ≤ (sharedN02700MinusP026Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP026BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP026Output2556,
    kernelN02700MinusP026Center2555, kernelN02700MinusP026Error2555, embedPair2542]

theorem sharedN02700MinusP026Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP026Output2556.1) + embedPair2542
            sharedN02700MinusP026Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP026Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP026Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP026Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP026Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP026Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP026Output2556, pairMagnitude2542]

def sharedN02700MinusP027Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP027Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP027Output2556.1‖ ≤ (sharedN02700MinusP027Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP027BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP027Output2556,
    kernelN02700MinusP027Center2555, kernelN02700MinusP027Error2555, embedPair2542]

theorem sharedN02700MinusP027Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP027Output2556.1) + embedPair2542
            sharedN02700MinusP027Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP027Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP027Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP027Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP027Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP027Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP027Output2556, pairMagnitude2542]

def sharedN02700MinusP028Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP028Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP028Output2556.1‖ ≤ (sharedN02700MinusP028Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP028BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP028Output2556,
    kernelN02700MinusP028Center2555, kernelN02700MinusP028Error2555, embedPair2542]

theorem sharedN02700MinusP028Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP028Output2556.1) + embedPair2542
            sharedN02700MinusP028Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP028Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP028Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP028Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP028Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP028Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP028Output2556, pairMagnitude2542]

def sharedN02700MinusP029Output2556 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem sharedN02700MinusP029Error2556 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP029Output2556.1‖ ≤ (sharedN02700MinusP029Output2556.2 : ℝ) := by
  have h := kernelN02700MinusP029BaseError2555
  convert h using 1
  all_goals norm_num [sharedN02700MinusPosition2556, kernelN02700MinusPosition2555,
      sharedN02700MinusP029Output2556,
    kernelN02700MinusP029Center2555, kernelN02700MinusP029Error2555, embedPair2542]

theorem sharedN02700MinusP029Norm2556 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02700MinusPosition2556‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02700MinusPosition2556‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP029Output2556.1) + embedPair2542
            sharedN02700MinusP029Output2556.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ sharedN02700MinusPosition2556 - embedPair2542
            sharedN02700MinusP029Output2556.1‖ + ‖embedPair2542
            sharedN02700MinusP029Output2556.1‖ := norm_add_le _ _
    _ ≤ (sharedN02700MinusP029Output2556.2 : ℝ) + (pairMagnitude2542
        sharedN02700MinusP029Output2556.1 : ℝ) :=
      add_le_add sharedN02700MinusP029Error2556 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [sharedN02700MinusP029Output2556, pairMagnitude2542]

noncomputable def sharedN02700MinusValue2556 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 sharedN02700MinusP000Output2556.1
  | 1 => embedPair2542 sharedN02700MinusP001Output2556.1
  | 2 => embedPair2542 sharedN02700MinusP002Output2556.1
  | 3 => embedPair2542 sharedN02700MinusP003Output2556.1
  | 4 => embedPair2542 sharedN02700MinusP004Output2556.1
  | 5 => embedPair2542 sharedN02700MinusP005Output2556.1
  | 6 => embedPair2542 sharedN02700MinusP006Output2556.1
  | 7 => embedPair2542 sharedN02700MinusP007Output2556.1
  | 8 => embedPair2542 sharedN02700MinusP008Output2556.1
  | 9 => embedPair2542 sharedN02700MinusP009Output2556.1
  | 10 => embedPair2542 sharedN02700MinusP010Output2556.1
  | 11 => embedPair2542 sharedN02700MinusP011Output2556.1
  | 12 => embedPair2542 sharedN02700MinusP012Output2556.1
  | 13 => embedPair2542 sharedN02700MinusP013Output2556.1
  | 14 => embedPair2542 sharedN02700MinusP014Output2556.1
  | 15 => embedPair2542 sharedN02700MinusP015Output2556.1
  | 16 => embedPair2542 sharedN02700MinusP016Output2556.1
  | 17 => embedPair2542 sharedN02700MinusP017Output2556.1
  | 18 => embedPair2542 sharedN02700MinusP018Output2556.1
  | 19 => embedPair2542 sharedN02700MinusP019Output2556.1
  | 20 => embedPair2542 sharedN02700MinusP020Output2556.1
  | 21 => embedPair2542 sharedN02700MinusP021Output2556.1
  | 22 => embedPair2542 sharedN02700MinusP022Output2556.1
  | 23 => embedPair2542 sharedN02700MinusP023Output2556.1
  | 24 => embedPair2542 sharedN02700MinusP024Output2556.1
  | 25 => embedPair2542 sharedN02700MinusP025Output2556.1
  | 26 => embedPair2542 sharedN02700MinusP026Output2556.1
  | 27 => embedPair2542 sharedN02700MinusP027Output2556.1
  | 28 => embedPair2542 sharedN02700MinusP028Output2556.1
  | 29 => embedPair2542 sharedN02700MinusP029Output2556.1
  | _ => 0

noncomputable def sharedN02700MinusError2556 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (sharedN02700MinusP000Output2556.2 : ℝ)
  | 1 => (sharedN02700MinusP001Output2556.2 : ℝ)
  | 2 => (sharedN02700MinusP002Output2556.2 : ℝ)
  | 3 => (sharedN02700MinusP003Output2556.2 : ℝ)
  | 4 => (sharedN02700MinusP004Output2556.2 : ℝ)
  | 5 => (sharedN02700MinusP005Output2556.2 : ℝ)
  | 6 => (sharedN02700MinusP006Output2556.2 : ℝ)
  | 7 => (sharedN02700MinusP007Output2556.2 : ℝ)
  | 8 => (sharedN02700MinusP008Output2556.2 : ℝ)
  | 9 => (sharedN02700MinusP009Output2556.2 : ℝ)
  | 10 => (sharedN02700MinusP010Output2556.2 : ℝ)
  | 11 => (sharedN02700MinusP011Output2556.2 : ℝ)
  | 12 => (sharedN02700MinusP012Output2556.2 : ℝ)
  | 13 => (sharedN02700MinusP013Output2556.2 : ℝ)
  | 14 => (sharedN02700MinusP014Output2556.2 : ℝ)
  | 15 => (sharedN02700MinusP015Output2556.2 : ℝ)
  | 16 => (sharedN02700MinusP016Output2556.2 : ℝ)
  | 17 => (sharedN02700MinusP017Output2556.2 : ℝ)
  | 18 => (sharedN02700MinusP018Output2556.2 : ℝ)
  | 19 => (sharedN02700MinusP019Output2556.2 : ℝ)
  | 20 => (sharedN02700MinusP020Output2556.2 : ℝ)
  | 21 => (sharedN02700MinusP021Output2556.2 : ℝ)
  | 22 => (sharedN02700MinusP022Output2556.2 : ℝ)
  | 23 => (sharedN02700MinusP023Output2556.2 : ℝ)
  | 24 => (sharedN02700MinusP024Output2556.2 : ℝ)
  | 25 => (sharedN02700MinusP025Output2556.2 : ℝ)
  | 26 => (sharedN02700MinusP026Output2556.2 : ℝ)
  | 27 => (sharedN02700MinusP027Output2556.2 : ℝ)
  | 28 => (sharedN02700MinusP028Output2556.2 : ℝ)
  | 29 => (sharedN02700MinusP029Output2556.2 : ℝ)
  | _ => 0

theorem sharedN02700MinusExp_error2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN02700MinusPosition2556 - sharedN02700MinusValue2556 i‖
            ≤ sharedN02700MinusError2556 i := by
  fin_cases i
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP000Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP001Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP002Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP003Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP004Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP005Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP006Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP007Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP008Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP009Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP010Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP011Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP012Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP013Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP014Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP015Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP016Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP017Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP018Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP019Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP020Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP021Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP022Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP023Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP024Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP025Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP026Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP027Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP028Error2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP029Error2556

theorem sharedN02700MinusUnit_norm2556 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN02700MinusPosition2556‖ ≤ 1 := by
  fin_cases i
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP000Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP001Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP002Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP003Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP004Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP005Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP006Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP007Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP008Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP009Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP010Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP011Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP012Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP013Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP014Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP015Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP016Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP017Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP018Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP019Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP020Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP021Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP022Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP023Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP024Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP025Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP026Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP027Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP028Norm2556
  · simpa only [sharedN02700MinusValue2556, sharedN02700MinusError2556] using
      sharedN02700MinusP029Norm2556

noncomputable def sharedN02700MinusSumValue2556 : ℂ := ⟨(((((92579276035265395592 * 10^40
        + 7873072319802168597440769213438413023552) * 10^40
        + 9814253324359234648482434609233726500941) * 10^40
        + 7721401264954437094476196760552775256569) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816)),
    (((((4332664037283799720 * 10^40
        + 9880388145859937457707809373382432151985) * 10^40
        + 5453602488198406223493266272973028526152) * 10^40
        + 3944166073585142655029522549679794244257) : ℝ) /
        (((6243497100631984462763194 * 10^40
        + 4595863326114971962853299423017183139192) * 10^40
        + 5074347763953124024061220612698394231965) * 10^40
        + 3862242813245790895951358576570612580352))⟩

noncomputable def sharedN02700MinusUpper2556 : ℝ := ((19793 : ℝ) /
        10000000000)

theorem sharedN02700MinusSum_eq2556 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN02700MinusValue2556 i) =
      sharedN02700MinusSumValue2556 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN02700MinusValue2556,
      sharedN02700MinusSumValue2556, embedPair2542, sharedN02700MinusP000Output2556,
      sharedN02700MinusP001Output2556,
      sharedN02700MinusP002Output2556,
      sharedN02700MinusP003Output2556,
      sharedN02700MinusP004Output2556,
      sharedN02700MinusP005Output2556,
      sharedN02700MinusP006Output2556,
      sharedN02700MinusP007Output2556,
      sharedN02700MinusP008Output2556,
      sharedN02700MinusP009Output2556,
      sharedN02700MinusP010Output2556,
      sharedN02700MinusP011Output2556,
      sharedN02700MinusP012Output2556,
      sharedN02700MinusP013Output2556,
      sharedN02700MinusP014Output2556,
      sharedN02700MinusP015Output2556,
      sharedN02700MinusP016Output2556,
      sharedN02700MinusP017Output2556,
      sharedN02700MinusP018Output2556,
      sharedN02700MinusP019Output2556,
      sharedN02700MinusP020Output2556,
      sharedN02700MinusP021Output2556,
      sharedN02700MinusP022Output2556,
      sharedN02700MinusP023Output2556,
      sharedN02700MinusP024Output2556,
      sharedN02700MinusP025Output2556,
      sharedN02700MinusP026Output2556,
      sharedN02700MinusP027Output2556,
      sharedN02700MinusP028Output2556,
      sharedN02700MinusP029Output2556, Complex.mul_re, Complex.mul_im]

theorem sharedN02700MinusSum_norm2556 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN02700MinusValue2556 i‖ ≤
      ((1237 : ℝ) /
        625000000) := by
  rw [sharedN02700MinusSum_eq2556]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [sharedN02700MinusSumValue2556]

theorem sharedN02700MinusEvaluation_charge2556 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * sharedN02700MinusError2556 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, sharedN02700MinusError2556,
      sharedN02700MinusP000Output2556,
      sharedN02700MinusP001Output2556,
      sharedN02700MinusP002Output2556,
      sharedN02700MinusP003Output2556,
      sharedN02700MinusP004Output2556,
      sharedN02700MinusP005Output2556,
      sharedN02700MinusP006Output2556,
      sharedN02700MinusP007Output2556,
      sharedN02700MinusP008Output2556,
      sharedN02700MinusP009Output2556,
      sharedN02700MinusP010Output2556,
      sharedN02700MinusP011Output2556,
      sharedN02700MinusP012Output2556,
      sharedN02700MinusP013Output2556,
      sharedN02700MinusP014Output2556,
      sharedN02700MinusP015Output2556,
      sharedN02700MinusP016Output2556,
      sharedN02700MinusP017Output2556,
      sharedN02700MinusP018Output2556,
      sharedN02700MinusP019Output2556,
      sharedN02700MinusP020Output2556,
      sharedN02700MinusP021Output2556,
      sharedN02700MinusP022Output2556,
      sharedN02700MinusP023Output2556,
      sharedN02700MinusP024Output2556,
      sharedN02700MinusP025Output2556,
      sharedN02700MinusP026Output2556,
      sharedN02700MinusP027Output2556,
      sharedN02700MinusP028Output2556,
      sharedN02700MinusP029Output2556]

theorem sharedN02700MinusSigned_le2556 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 sharedN02700MinusPosition2556 ≤ sharedN02700MinusUpper2556 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN02700MinusPosition2556‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * sharedN02700MinusValue2556 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * sharedN02700MinusError2556 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (sharedN02700MinusExp_error2556 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN02700MinusPosition2556‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (sharedN02700MinusUnit_norm2556 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i sharedN02700MinusPosition2556‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 sharedN02700MinusUpper2556
  linarith [sharedN02700MinusSum_norm2556, sharedN02700MinusEvaluation_charge2556]

theorem sharedN02700MinusPhysical_le2556 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 sharedN02700MinusPosition2556‖ ≤
      sharedN02700MinusUpper2556 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        sharedN02700MinusPosition2556
  simpa only [iteratedDeriv_zero] using h.trans sharedN02700MinusSigned_le2556

theorem sharedN02700MinusGrid2556 :
    -stripRadius2303 + (2700 : ℝ)*(2*stripRadius2303/10240) = sharedN02700MinusPosition2556 :=
        by
  norm_num [stripRadius2303, sharedN02700MinusPosition2556]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.sharedN02700MinusSigned_le2556
#print axioms ConnesWeilRH.Dev.sharedN02700MinusPhysical_le2556
