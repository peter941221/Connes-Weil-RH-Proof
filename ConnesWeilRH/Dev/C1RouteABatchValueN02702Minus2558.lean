import ConnesWeilRH.Dev.C1RouteABatchN02702Minus2558
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchValueN02702MinusPosition2558 : ℝ := (((-79233025209) : ℝ) /
        25600000000)

def batchValueN02702MinusP000Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem batchValueN02702MinusP000Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP000Output2558.1‖ ≤ (batchValueN02702MinusP000Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP000BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP000Output2558,
    batchN02702MinusP000Center2558, batchN02702MinusP000Error2558, embedPair2542]

theorem batchValueN02702MinusP000Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP000Output2558.1) + embedPair2542
            batchValueN02702MinusP000Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP000Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP000Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP000Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP000Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP000Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP000Output2558, pairMagnitude2542]

def batchValueN02702MinusP001Output2558 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP001Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP001Output2558.1‖ ≤ (batchValueN02702MinusP001Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP001BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP001Output2558,
    batchN02702MinusP001Center2558, batchN02702MinusP001Error2558, embedPair2542]

theorem batchValueN02702MinusP001Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP001Output2558.1) + embedPair2542
            batchValueN02702MinusP001Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP001Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP001Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP001Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP001Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP001Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP001Output2558, pairMagnitude2542]

def batchValueN02702MinusP002Output2558 : RatState2542 :=
  (((((-1808320510932834055125) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-3040243993904768592253) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((26203547001217881765 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN02702MinusP002Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP002Output2558.1‖ ≤ (batchValueN02702MinusP002Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP002BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP002Output2558,
    batchN02702MinusP002Center2558, batchN02702MinusP002Error2558, embedPair2542]

theorem batchValueN02702MinusP002Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP002Output2558.1) + embedPair2542
            batchValueN02702MinusP002Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP002Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP002Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP002Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP002Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP002Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP002Output2558, pairMagnitude2542]

def batchValueN02702MinusP003Output2558 : RatState2542 :=
  (((((-120309152640455605580363375995) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-202270104506104807991901408963) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((408428881659359733954910165 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN02702MinusP003Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP003Output2558.1‖ ≤ (batchValueN02702MinusP003Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP003BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP003Output2558,
    batchN02702MinusP003Center2558, batchN02702MinusP003Error2558, embedPair2542]

theorem batchValueN02702MinusP003Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP003Output2558.1) + embedPair2542
            batchValueN02702MinusP003Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP003Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP003Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP003Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP003Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP003Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP003Output2558, pairMagnitude2542]

def batchValueN02702MinusP004Output2558 : RatState2542 :=
  (((((-29892566899523530686861247311731) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((100513925965249929978375590473809 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((198097311830982059347853453109 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN02702MinusP004Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP004Output2558.1‖ ≤ (batchValueN02702MinusP004Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP004BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP004Output2558,
    batchN02702MinusP004Center2558, batchN02702MinusP004Error2558, embedPair2542]

theorem batchValueN02702MinusP004Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP004Output2558.1) + embedPair2542
            batchValueN02702MinusP004Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP004Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP004Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP004Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP004Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP004Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP004Output2558, pairMagnitude2542]

def batchValueN02702MinusP005Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem batchValueN02702MinusP005Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP005Output2558.1‖ ≤ (batchValueN02702MinusP005Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP005BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP005Output2558,
    batchN02702MinusP005Center2558, batchN02702MinusP005Error2558, embedPair2542]

theorem batchValueN02702MinusP005Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP005Output2558.1) + embedPair2542
            batchValueN02702MinusP005Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP005Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP005Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP005Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP005Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP005Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP005Output2558, pairMagnitude2542]

def batchValueN02702MinusP006Output2558 : RatState2542 :=
  ((((11719533816037623 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((4021762308289 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN02702MinusP006Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP006Output2558.1‖ ≤ (batchValueN02702MinusP006Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP006BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP006Output2558,
    batchN02702MinusP006Center2558, batchN02702MinusP006Error2558, embedPair2542]

theorem batchValueN02702MinusP006Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP006Output2558.1) + embedPair2542
            batchValueN02702MinusP006Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP006Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP006Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP006Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP006Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP006Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP006Output2558, pairMagnitude2542]

def batchValueN02702MinusP007Output2558 : RatState2542 :=
  ((((117672731958146325856108455551 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((16281624050426687031899557 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN02702MinusP007Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP007Output2558.1‖ ≤ (batchValueN02702MinusP007Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP007BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP007Output2558,
    batchN02702MinusP007Center2558, batchN02702MinusP007Error2558, embedPair2542]

theorem batchValueN02702MinusP007Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP007Output2558.1) + embedPair2542
            batchValueN02702MinusP007Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP007Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP007Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP007Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP007Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP007Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP007Output2558, pairMagnitude2542]

def batchValueN02702MinusP008Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP008Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP008Output2558.1‖ ≤ (batchValueN02702MinusP008Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP008BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP008Output2558,
    batchN02702MinusP008Center2558, batchN02702MinusP008Error2558, embedPair2542]

theorem batchValueN02702MinusP008Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP008Output2558.1) + embedPair2542
            batchValueN02702MinusP008Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP008Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP008Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP008Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP008Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP008Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP008Output2558, pairMagnitude2542]

def batchValueN02702MinusP009Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP009Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP009Output2558.1‖ ≤ (batchValueN02702MinusP009Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP009BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP009Output2558,
    batchN02702MinusP009Center2558, batchN02702MinusP009Error2558, embedPair2542]

theorem batchValueN02702MinusP009Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP009Output2558.1) + embedPair2542
            batchValueN02702MinusP009Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP009Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP009Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP009Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP009Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP009Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP009Output2558, pairMagnitude2542]

def batchValueN02702MinusP010Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP010Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP010Output2558.1‖ ≤ (batchValueN02702MinusP010Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP010BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP010Output2558,
    batchN02702MinusP010Center2558, batchN02702MinusP010Error2558, embedPair2542]

theorem batchValueN02702MinusP010Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP010Output2558.1) + embedPair2542
            batchValueN02702MinusP010Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP010Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP010Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP010Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP010Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP010Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP010Output2558, pairMagnitude2542]

def batchValueN02702MinusP011Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP011Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP011Output2558.1‖ ≤ (batchValueN02702MinusP011Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP011BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP011Output2558,
    batchN02702MinusP011Center2558, batchN02702MinusP011Error2558, embedPair2542]

theorem batchValueN02702MinusP011Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP011Output2558.1) + embedPair2542
            batchValueN02702MinusP011Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP011Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP011Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP011Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP011Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP011Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP011Output2558, pairMagnitude2542]

def batchValueN02702MinusP012Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP012Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP012Output2558.1‖ ≤ (batchValueN02702MinusP012Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP012BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP012Output2558,
    batchN02702MinusP012Center2558, batchN02702MinusP012Error2558, embedPair2542]

theorem batchValueN02702MinusP012Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP012Output2558.1) + embedPair2542
            batchValueN02702MinusP012Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP012Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP012Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP012Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP012Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP012Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP012Output2558, pairMagnitude2542]

def batchValueN02702MinusP013Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP013Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP013Output2558.1‖ ≤ (batchValueN02702MinusP013Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP013BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP013Output2558,
    batchN02702MinusP013Center2558, batchN02702MinusP013Error2558, embedPair2542]

theorem batchValueN02702MinusP013Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP013Output2558.1) + embedPair2542
            batchValueN02702MinusP013Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP013Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP013Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP013Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP013Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP013Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP013Output2558, pairMagnitude2542]

def batchValueN02702MinusP014Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP014Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP014Output2558.1‖ ≤ (batchValueN02702MinusP014Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP014BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP014Output2558,
    batchN02702MinusP014Center2558, batchN02702MinusP014Error2558, embedPair2542]

theorem batchValueN02702MinusP014Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP014Output2558.1) + embedPair2542
            batchValueN02702MinusP014Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP014Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP014Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP014Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP014Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP014Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP014Output2558, pairMagnitude2542]

def batchValueN02702MinusP015Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP015Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP015Output2558.1‖ ≤ (batchValueN02702MinusP015Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP015BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP015Output2558,
    batchN02702MinusP015Center2558, batchN02702MinusP015Error2558, embedPair2542]

theorem batchValueN02702MinusP015Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP015Output2558.1) + embedPair2542
            batchValueN02702MinusP015Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP015Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP015Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP015Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP015Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP015Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP015Output2558, pairMagnitude2542]

def batchValueN02702MinusP016Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP016Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP016Output2558.1‖ ≤ (batchValueN02702MinusP016Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP016BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP016Output2558,
    batchN02702MinusP016Center2558, batchN02702MinusP016Error2558, embedPair2542]

theorem batchValueN02702MinusP016Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP016Output2558.1) + embedPair2542
            batchValueN02702MinusP016Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP016Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP016Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP016Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP016Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP016Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP016Output2558, pairMagnitude2542]

def batchValueN02702MinusP017Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP017Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP017Output2558.1‖ ≤ (batchValueN02702MinusP017Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP017BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP017Output2558,
    batchN02702MinusP017Center2558, batchN02702MinusP017Error2558, embedPair2542]

theorem batchValueN02702MinusP017Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP017Output2558.1) + embedPair2542
            batchValueN02702MinusP017Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP017Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP017Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP017Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP017Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP017Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP017Output2558, pairMagnitude2542]

def batchValueN02702MinusP018Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP018Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP018Output2558.1‖ ≤ (batchValueN02702MinusP018Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP018BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP018Output2558,
    batchN02702MinusP018Center2558, batchN02702MinusP018Error2558, embedPair2542]

theorem batchValueN02702MinusP018Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP018Output2558.1) + embedPair2542
            batchValueN02702MinusP018Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP018Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP018Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP018Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP018Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP018Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP018Output2558, pairMagnitude2542]

def batchValueN02702MinusP019Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP019Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP019Output2558.1‖ ≤ (batchValueN02702MinusP019Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP019BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP019Output2558,
    batchN02702MinusP019Center2558, batchN02702MinusP019Error2558, embedPair2542]

theorem batchValueN02702MinusP019Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP019Output2558.1) + embedPair2542
            batchValueN02702MinusP019Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP019Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP019Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP019Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP019Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP019Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP019Output2558, pairMagnitude2542]

def batchValueN02702MinusP020Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP020Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP020Output2558.1‖ ≤ (batchValueN02702MinusP020Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP020BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP020Output2558,
    batchN02702MinusP020Center2558, batchN02702MinusP020Error2558, embedPair2542]

theorem batchValueN02702MinusP020Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP020Output2558.1) + embedPair2542
            batchValueN02702MinusP020Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP020Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP020Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP020Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP020Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP020Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP020Output2558, pairMagnitude2542]

def batchValueN02702MinusP021Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP021Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP021Output2558.1‖ ≤ (batchValueN02702MinusP021Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP021BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP021Output2558,
    batchN02702MinusP021Center2558, batchN02702MinusP021Error2558, embedPair2542]

theorem batchValueN02702MinusP021Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP021Output2558.1) + embedPair2542
            batchValueN02702MinusP021Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP021Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP021Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP021Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP021Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP021Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP021Output2558, pairMagnitude2542]

def batchValueN02702MinusP022Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP022Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP022Output2558.1‖ ≤ (batchValueN02702MinusP022Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP022BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP022Output2558,
    batchN02702MinusP022Center2558, batchN02702MinusP022Error2558, embedPair2542]

theorem batchValueN02702MinusP022Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP022Output2558.1) + embedPair2542
            batchValueN02702MinusP022Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP022Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP022Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP022Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP022Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP022Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP022Output2558, pairMagnitude2542]

def batchValueN02702MinusP023Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP023Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP023Output2558.1‖ ≤ (batchValueN02702MinusP023Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP023BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP023Output2558,
    batchN02702MinusP023Center2558, batchN02702MinusP023Error2558, embedPair2542]

theorem batchValueN02702MinusP023Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP023Output2558.1) + embedPair2542
            batchValueN02702MinusP023Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP023Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP023Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP023Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP023Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP023Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP023Output2558, pairMagnitude2542]

def batchValueN02702MinusP024Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP024Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP024Output2558.1‖ ≤ (batchValueN02702MinusP024Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP024BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP024Output2558,
    batchN02702MinusP024Center2558, batchN02702MinusP024Error2558, embedPair2542]

theorem batchValueN02702MinusP024Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP024Output2558.1) + embedPair2542
            batchValueN02702MinusP024Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP024Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP024Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP024Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP024Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP024Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP024Output2558, pairMagnitude2542]

def batchValueN02702MinusP025Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP025Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP025Output2558.1‖ ≤ (batchValueN02702MinusP025Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP025BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP025Output2558,
    batchN02702MinusP025Center2558, batchN02702MinusP025Error2558, embedPair2542]

theorem batchValueN02702MinusP025Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP025Output2558.1) + embedPair2542
            batchValueN02702MinusP025Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP025Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP025Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP025Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP025Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP025Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP025Output2558, pairMagnitude2542]

def batchValueN02702MinusP026Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP026Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP026Output2558.1‖ ≤ (batchValueN02702MinusP026Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP026BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP026Output2558,
    batchN02702MinusP026Center2558, batchN02702MinusP026Error2558, embedPair2542]

theorem batchValueN02702MinusP026Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP026Output2558.1) + embedPair2542
            batchValueN02702MinusP026Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP026Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP026Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP026Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP026Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP026Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP026Output2558, pairMagnitude2542]

def batchValueN02702MinusP027Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP027Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP027Output2558.1‖ ≤ (batchValueN02702MinusP027Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP027BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP027Output2558,
    batchN02702MinusP027Center2558, batchN02702MinusP027Error2558, embedPair2542]

theorem batchValueN02702MinusP027Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP027Output2558.1) + embedPair2542
            batchValueN02702MinusP027Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP027Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP027Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP027Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP027Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP027Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP027Output2558, pairMagnitude2542]

def batchValueN02702MinusP028Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP028Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP028Output2558.1‖ ≤ (batchValueN02702MinusP028Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP028BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP028Output2558,
    batchN02702MinusP028Center2558, batchN02702MinusP028Error2558, embedPair2542]

theorem batchValueN02702MinusP028Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP028Output2558.1) + embedPair2542
            batchValueN02702MinusP028Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP028Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP028Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP028Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP028Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP028Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP028Output2558, pairMagnitude2542]

def batchValueN02702MinusP029Output2558 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02702MinusP029Error2558 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP029Output2558.1‖ ≤ (batchValueN02702MinusP029Output2558.2 : ℝ)
                := by
  have h := batchN02702MinusP029BaseError2558
  convert h using 1
  all_goals norm_num [batchValueN02702MinusPosition2558, batchN02702MinusPosition2558,
      batchValueN02702MinusP029Output2558,
    batchN02702MinusP029Center2558, batchN02702MinusP029Error2558, embedPair2542]

theorem batchValueN02702MinusP029Norm2558 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02702MinusPosition2558‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02702MinusPosition2558‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP029Output2558.1) + embedPair2542
            batchValueN02702MinusP029Output2558.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02702MinusPosition2558 - embedPair2542
            batchValueN02702MinusP029Output2558.1‖ + ‖embedPair2542
            batchValueN02702MinusP029Output2558.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02702MinusP029Output2558.2 : ℝ) + (pairMagnitude2542
        batchValueN02702MinusP029Output2558.1 : ℝ) :=
      add_le_add batchValueN02702MinusP029Error2558 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02702MinusP029Output2558, pairMagnitude2542]

noncomputable def batchValueN02702MinusValue2558 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchValueN02702MinusP000Output2558.1
  | 1 => embedPair2542 batchValueN02702MinusP001Output2558.1
  | 2 => embedPair2542 batchValueN02702MinusP002Output2558.1
  | 3 => embedPair2542 batchValueN02702MinusP003Output2558.1
  | 4 => embedPair2542 batchValueN02702MinusP004Output2558.1
  | 5 => embedPair2542 batchValueN02702MinusP005Output2558.1
  | 6 => embedPair2542 batchValueN02702MinusP006Output2558.1
  | 7 => embedPair2542 batchValueN02702MinusP007Output2558.1
  | 8 => embedPair2542 batchValueN02702MinusP008Output2558.1
  | 9 => embedPair2542 batchValueN02702MinusP009Output2558.1
  | 10 => embedPair2542 batchValueN02702MinusP010Output2558.1
  | 11 => embedPair2542 batchValueN02702MinusP011Output2558.1
  | 12 => embedPair2542 batchValueN02702MinusP012Output2558.1
  | 13 => embedPair2542 batchValueN02702MinusP013Output2558.1
  | 14 => embedPair2542 batchValueN02702MinusP014Output2558.1
  | 15 => embedPair2542 batchValueN02702MinusP015Output2558.1
  | 16 => embedPair2542 batchValueN02702MinusP016Output2558.1
  | 17 => embedPair2542 batchValueN02702MinusP017Output2558.1
  | 18 => embedPair2542 batchValueN02702MinusP018Output2558.1
  | 19 => embedPair2542 batchValueN02702MinusP019Output2558.1
  | 20 => embedPair2542 batchValueN02702MinusP020Output2558.1
  | 21 => embedPair2542 batchValueN02702MinusP021Output2558.1
  | 22 => embedPair2542 batchValueN02702MinusP022Output2558.1
  | 23 => embedPair2542 batchValueN02702MinusP023Output2558.1
  | 24 => embedPair2542 batchValueN02702MinusP024Output2558.1
  | 25 => embedPair2542 batchValueN02702MinusP025Output2558.1
  | 26 => embedPair2542 batchValueN02702MinusP026Output2558.1
  | 27 => embedPair2542 batchValueN02702MinusP027Output2558.1
  | 28 => embedPair2542 batchValueN02702MinusP028Output2558.1
  | 29 => embedPair2542 batchValueN02702MinusP029Output2558.1
  | _ => 0

noncomputable def batchValueN02702MinusError2558 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (batchValueN02702MinusP000Output2558.2 : ℝ)
  | 1 => (batchValueN02702MinusP001Output2558.2 : ℝ)
  | 2 => (batchValueN02702MinusP002Output2558.2 : ℝ)
  | 3 => (batchValueN02702MinusP003Output2558.2 : ℝ)
  | 4 => (batchValueN02702MinusP004Output2558.2 : ℝ)
  | 5 => (batchValueN02702MinusP005Output2558.2 : ℝ)
  | 6 => (batchValueN02702MinusP006Output2558.2 : ℝ)
  | 7 => (batchValueN02702MinusP007Output2558.2 : ℝ)
  | 8 => (batchValueN02702MinusP008Output2558.2 : ℝ)
  | 9 => (batchValueN02702MinusP009Output2558.2 : ℝ)
  | 10 => (batchValueN02702MinusP010Output2558.2 : ℝ)
  | 11 => (batchValueN02702MinusP011Output2558.2 : ℝ)
  | 12 => (batchValueN02702MinusP012Output2558.2 : ℝ)
  | 13 => (batchValueN02702MinusP013Output2558.2 : ℝ)
  | 14 => (batchValueN02702MinusP014Output2558.2 : ℝ)
  | 15 => (batchValueN02702MinusP015Output2558.2 : ℝ)
  | 16 => (batchValueN02702MinusP016Output2558.2 : ℝ)
  | 17 => (batchValueN02702MinusP017Output2558.2 : ℝ)
  | 18 => (batchValueN02702MinusP018Output2558.2 : ℝ)
  | 19 => (batchValueN02702MinusP019Output2558.2 : ℝ)
  | 20 => (batchValueN02702MinusP020Output2558.2 : ℝ)
  | 21 => (batchValueN02702MinusP021Output2558.2 : ℝ)
  | 22 => (batchValueN02702MinusP022Output2558.2 : ℝ)
  | 23 => (batchValueN02702MinusP023Output2558.2 : ℝ)
  | 24 => (batchValueN02702MinusP024Output2558.2 : ℝ)
  | 25 => (batchValueN02702MinusP025Output2558.2 : ℝ)
  | 26 => (batchValueN02702MinusP026Output2558.2 : ℝ)
  | 27 => (batchValueN02702MinusP027Output2558.2 : ℝ)
  | 28 => (batchValueN02702MinusP028Output2558.2 : ℝ)
  | 29 => (batchValueN02702MinusP029Output2558.2 : ℝ)
  | _ => 0

theorem batchValueN02702MinusExp_error2558 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02702MinusPosition2558 -
            batchValueN02702MinusValue2558 i‖
            ≤ batchValueN02702MinusError2558 i := by
  fin_cases i
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP000Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP001Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP002Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP003Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP004Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP005Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP006Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP007Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP008Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP009Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP010Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP011Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP012Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP013Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP014Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP015Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP016Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP017Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP018Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP019Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP020Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP021Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP022Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP023Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP024Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP025Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP026Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP027Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP028Error2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP029Error2558

theorem batchValueN02702MinusUnit_norm2558 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02702MinusPosition2558‖ ≤ 1 := by
  fin_cases i
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP000Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP001Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP002Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP003Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP004Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP005Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP006Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP007Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP008Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP009Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP010Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP011Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP012Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP013Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP014Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP015Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP016Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP017Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP018Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP019Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP020Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP021Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP022Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP023Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP024Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP025Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP026Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP027Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP028Norm2558
  · simpa only [batchValueN02702MinusValue2558, batchValueN02702MinusError2558] using
      batchValueN02702MinusP029Norm2558

noncomputable def batchValueN02702MinusSumValue2558 : ℂ := ⟨(((((5320613044688474445 * 10^40
        + 2917546329029105235856271502122355178564) * 10^40
        + 9793857984722880907300187747641040450119) * 10^40
        + 5430677424993232404023078772766157461637) : ℝ) /
        (((3121748550315992231381597 * 10^40
        + 2297931663057485981426649711508591569596) * 10^40
        + 2537173881976562012030610306349197115982) * 10^40
        + 6931121406622895447975679288285306290176)),
    (((((2415824296142789034 * 10^40
        + 5518583474141964128622276703053789478606) * 10^40
        + 2775124808454351594546197529129105049674) * 10^40
        + 5379406072765778143307514571656797283719) : ℝ) /
        (((3121748550315992231381597 * 10^40
        + 2297931663057485981426649711508591569596) * 10^40
        + 2537173881976562012030610306349197115982) * 10^40
        + 6931121406622895447975679288285306290176))⟩

noncomputable def batchValueN02702MinusUpper2558 : ℝ := ((117 : ℝ) /
        62500000)

theorem batchValueN02702MinusSum_eq2558 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02702MinusValue2558 i) =
      batchValueN02702MinusSumValue2558 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN02702MinusValue2558,
      batchValueN02702MinusSumValue2558, embedPair2542, batchValueN02702MinusP000Output2558,
      batchValueN02702MinusP001Output2558,
      batchValueN02702MinusP002Output2558,
      batchValueN02702MinusP003Output2558,
      batchValueN02702MinusP004Output2558,
      batchValueN02702MinusP005Output2558,
      batchValueN02702MinusP006Output2558,
      batchValueN02702MinusP007Output2558,
      batchValueN02702MinusP008Output2558,
      batchValueN02702MinusP009Output2558,
      batchValueN02702MinusP010Output2558,
      batchValueN02702MinusP011Output2558,
      batchValueN02702MinusP012Output2558,
      batchValueN02702MinusP013Output2558,
      batchValueN02702MinusP014Output2558,
      batchValueN02702MinusP015Output2558,
      batchValueN02702MinusP016Output2558,
      batchValueN02702MinusP017Output2558,
      batchValueN02702MinusP018Output2558,
      batchValueN02702MinusP019Output2558,
      batchValueN02702MinusP020Output2558,
      batchValueN02702MinusP021Output2558,
      batchValueN02702MinusP022Output2558,
      batchValueN02702MinusP023Output2558,
      batchValueN02702MinusP024Output2558,
      batchValueN02702MinusP025Output2558,
      batchValueN02702MinusP026Output2558,
      batchValueN02702MinusP027Output2558,
      batchValueN02702MinusP028Output2558,
      batchValueN02702MinusP029Output2558, Complex.mul_re, Complex.mul_im]

theorem batchValueN02702MinusSum_norm2558 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02702MinusValue2558 i‖ ≤
      ((18719 : ℝ) /
        10000000000) := by
  rw [batchValueN02702MinusSum_eq2558]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchValueN02702MinusSumValue2558]

theorem batchValueN02702MinusEvaluation_charge2558 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchValueN02702MinusError2558 i) ≤ (1 : ℝ)/10^12 :=
          by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN02702MinusError2558,
      batchValueN02702MinusP000Output2558,
      batchValueN02702MinusP001Output2558,
      batchValueN02702MinusP002Output2558,
      batchValueN02702MinusP003Output2558,
      batchValueN02702MinusP004Output2558,
      batchValueN02702MinusP005Output2558,
      batchValueN02702MinusP006Output2558,
      batchValueN02702MinusP007Output2558,
      batchValueN02702MinusP008Output2558,
      batchValueN02702MinusP009Output2558,
      batchValueN02702MinusP010Output2558,
      batchValueN02702MinusP011Output2558,
      batchValueN02702MinusP012Output2558,
      batchValueN02702MinusP013Output2558,
      batchValueN02702MinusP014Output2558,
      batchValueN02702MinusP015Output2558,
      batchValueN02702MinusP016Output2558,
      batchValueN02702MinusP017Output2558,
      batchValueN02702MinusP018Output2558,
      batchValueN02702MinusP019Output2558,
      batchValueN02702MinusP020Output2558,
      batchValueN02702MinusP021Output2558,
      batchValueN02702MinusP022Output2558,
      batchValueN02702MinusP023Output2558,
      batchValueN02702MinusP024Output2558,
      batchValueN02702MinusP025Output2558,
      batchValueN02702MinusP026Output2558,
      batchValueN02702MinusP027Output2558,
      batchValueN02702MinusP028Output2558,
      batchValueN02702MinusP029Output2558]

theorem batchValueN02702MinusSigned_le2558 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchValueN02702MinusPosition2558 ≤ batchValueN02702MinusUpper2558 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02702MinusPosition2558‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02702MinusValue2558 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchValueN02702MinusError2558 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (batchValueN02702MinusExp_error2558 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02702MinusPosition2558‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchValueN02702MinusUnit_norm2558 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02702MinusPosition2558‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchValueN02702MinusUpper2558
  linarith [batchValueN02702MinusSum_norm2558, batchValueN02702MinusEvaluation_charge2558]

theorem batchValueN02702MinusPhysical_le2558 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 batchValueN02702MinusPosition2558‖ ≤
      batchValueN02702MinusUpper2558 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchValueN02702MinusPosition2558
  simpa only [iteratedDeriv_zero] using h.trans batchValueN02702MinusSigned_le2558

theorem batchValueN02702MinusGrid2558 :
    -stripRadius2303 + (2702 : ℝ)*(2*stripRadius2303/10240) = batchValueN02702MinusPosition2558 :=
        by
  norm_num [stripRadius2303, batchValueN02702MinusPosition2558]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchValueN02702MinusSigned_le2558
#print axioms ConnesWeilRH.Dev.batchValueN02702MinusPhysical_le2558
