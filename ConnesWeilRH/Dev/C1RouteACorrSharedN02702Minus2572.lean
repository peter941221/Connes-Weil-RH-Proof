import ConnesWeilRH.Dev.C1RouteABatchN02702Minus2558
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def corrSharedN02702MinusPosition2572 : ℝ := (((-79233025209) : ℝ) /
        25600000000)

def corrSharedN02702MinusP000Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02702MinusP000Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP000Output2572.1‖ ≤ (corrSharedN02702MinusP000Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP000BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP000Output2572,
    batchN02702MinusP000Center2558, batchN02702MinusP000Error2558, embedPair2542]

theorem corrSharedN02702MinusP000Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP000Output2572.1) + embedPair2542
            corrSharedN02702MinusP000Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP000Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP000Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP000Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP000Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP000Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP000Output2572, pairMagnitude2542]

def corrSharedN02702MinusP001Output2572 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP001Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP001Output2572.1‖ ≤ (corrSharedN02702MinusP001Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP001BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP001Output2572,
    batchN02702MinusP001Center2558, batchN02702MinusP001Error2558, embedPair2542]

theorem corrSharedN02702MinusP001Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP001Output2572.1) + embedPair2542
            corrSharedN02702MinusP001Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP001Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP001Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP001Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP001Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP001Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP001Output2572, pairMagnitude2542]

def corrSharedN02702MinusP002Output2572 : RatState2542 :=
  (((((-1808320510932834055125) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-3040243993904768592253) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((26203547001217881765 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem corrSharedN02702MinusP002Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP002Output2572.1‖ ≤ (corrSharedN02702MinusP002Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP002BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP002Output2572,
    batchN02702MinusP002Center2558, batchN02702MinusP002Error2558, embedPair2542]

theorem corrSharedN02702MinusP002Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP002Output2572.1) + embedPair2542
            corrSharedN02702MinusP002Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP002Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP002Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP002Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP002Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP002Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP002Output2572, pairMagnitude2542]

def corrSharedN02702MinusP003Output2572 : RatState2542 :=
  (((((-120309152640455605580363375995) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-202270104506104807991901408963) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((408428881659359733954910165 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem corrSharedN02702MinusP003Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP003Output2572.1‖ ≤ (corrSharedN02702MinusP003Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP003BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP003Output2572,
    batchN02702MinusP003Center2558, batchN02702MinusP003Error2558, embedPair2542]

theorem corrSharedN02702MinusP003Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP003Output2572.1) + embedPair2542
            corrSharedN02702MinusP003Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP003Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP003Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP003Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP003Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP003Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP003Output2572, pairMagnitude2542]

def corrSharedN02702MinusP004Output2572 : RatState2542 :=
  (((((-29892566899523530686861247311731) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((100513925965249929978375590473809 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((198097311830982059347853453109 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem corrSharedN02702MinusP004Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP004Output2572.1‖ ≤ (corrSharedN02702MinusP004Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP004BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP004Output2572,
    batchN02702MinusP004Center2558, batchN02702MinusP004Error2558, embedPair2542]

theorem corrSharedN02702MinusP004Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP004Output2572.1) + embedPair2542
            corrSharedN02702MinusP004Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP004Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP004Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP004Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP004Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP004Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP004Output2572, pairMagnitude2542]

def corrSharedN02702MinusP005Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem corrSharedN02702MinusP005Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP005Output2572.1‖ ≤ (corrSharedN02702MinusP005Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP005BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP005Output2572,
    batchN02702MinusP005Center2558, batchN02702MinusP005Error2558, embedPair2542]

theorem corrSharedN02702MinusP005Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP005Output2572.1) + embedPair2542
            corrSharedN02702MinusP005Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP005Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP005Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP005Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP005Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP005Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP005Output2572, pairMagnitude2542]

def corrSharedN02702MinusP006Output2572 : RatState2542 :=
  ((((11719533816037623 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((4021762308289 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem corrSharedN02702MinusP006Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP006Output2572.1‖ ≤ (corrSharedN02702MinusP006Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP006BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP006Output2572,
    batchN02702MinusP006Center2558, batchN02702MinusP006Error2558, embedPair2542]

theorem corrSharedN02702MinusP006Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP006Output2572.1) + embedPair2542
            corrSharedN02702MinusP006Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP006Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP006Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP006Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP006Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP006Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP006Output2572, pairMagnitude2542]

def corrSharedN02702MinusP007Output2572 : RatState2542 :=
  ((((117672731958146325856108455551 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((16281624050426687031899557 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem corrSharedN02702MinusP007Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP007Output2572.1‖ ≤ (corrSharedN02702MinusP007Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP007BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP007Output2572,
    batchN02702MinusP007Center2558, batchN02702MinusP007Error2558, embedPair2542]

theorem corrSharedN02702MinusP007Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP007Output2572.1) + embedPair2542
            corrSharedN02702MinusP007Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP007Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP007Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP007Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP007Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP007Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP007Output2572, pairMagnitude2542]

def corrSharedN02702MinusP008Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP008Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP008Output2572.1‖ ≤ (corrSharedN02702MinusP008Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP008BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP008Output2572,
    batchN02702MinusP008Center2558, batchN02702MinusP008Error2558, embedPair2542]

theorem corrSharedN02702MinusP008Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP008Output2572.1) + embedPair2542
            corrSharedN02702MinusP008Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP008Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP008Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP008Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP008Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP008Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP008Output2572, pairMagnitude2542]

def corrSharedN02702MinusP009Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP009Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP009Output2572.1‖ ≤ (corrSharedN02702MinusP009Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP009BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP009Output2572,
    batchN02702MinusP009Center2558, batchN02702MinusP009Error2558, embedPair2542]

theorem corrSharedN02702MinusP009Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP009Output2572.1) + embedPair2542
            corrSharedN02702MinusP009Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP009Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP009Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP009Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP009Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP009Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP009Output2572, pairMagnitude2542]

def corrSharedN02702MinusP010Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP010Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP010Output2572.1‖ ≤ (corrSharedN02702MinusP010Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP010BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP010Output2572,
    batchN02702MinusP010Center2558, batchN02702MinusP010Error2558, embedPair2542]

theorem corrSharedN02702MinusP010Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP010Output2572.1) + embedPair2542
            corrSharedN02702MinusP010Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP010Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP010Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP010Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP010Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP010Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP010Output2572, pairMagnitude2542]

def corrSharedN02702MinusP011Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP011Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP011Output2572.1‖ ≤ (corrSharedN02702MinusP011Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP011BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP011Output2572,
    batchN02702MinusP011Center2558, batchN02702MinusP011Error2558, embedPair2542]

theorem corrSharedN02702MinusP011Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP011Output2572.1) + embedPair2542
            corrSharedN02702MinusP011Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP011Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP011Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP011Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP011Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP011Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP011Output2572, pairMagnitude2542]

def corrSharedN02702MinusP012Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP012Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP012Output2572.1‖ ≤ (corrSharedN02702MinusP012Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP012BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP012Output2572,
    batchN02702MinusP012Center2558, batchN02702MinusP012Error2558, embedPair2542]

theorem corrSharedN02702MinusP012Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP012Output2572.1) + embedPair2542
            corrSharedN02702MinusP012Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP012Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP012Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP012Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP012Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP012Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP012Output2572, pairMagnitude2542]

def corrSharedN02702MinusP013Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP013Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP013Output2572.1‖ ≤ (corrSharedN02702MinusP013Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP013BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP013Output2572,
    batchN02702MinusP013Center2558, batchN02702MinusP013Error2558, embedPair2542]

theorem corrSharedN02702MinusP013Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP013Output2572.1) + embedPair2542
            corrSharedN02702MinusP013Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP013Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP013Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP013Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP013Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP013Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP013Output2572, pairMagnitude2542]

def corrSharedN02702MinusP014Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP014Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP014Output2572.1‖ ≤ (corrSharedN02702MinusP014Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP014BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP014Output2572,
    batchN02702MinusP014Center2558, batchN02702MinusP014Error2558, embedPair2542]

theorem corrSharedN02702MinusP014Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP014Output2572.1) + embedPair2542
            corrSharedN02702MinusP014Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP014Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP014Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP014Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP014Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP014Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP014Output2572, pairMagnitude2542]

def corrSharedN02702MinusP015Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP015Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP015Output2572.1‖ ≤ (corrSharedN02702MinusP015Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP015BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP015Output2572,
    batchN02702MinusP015Center2558, batchN02702MinusP015Error2558, embedPair2542]

theorem corrSharedN02702MinusP015Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP015Output2572.1) + embedPair2542
            corrSharedN02702MinusP015Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP015Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP015Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP015Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP015Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP015Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP015Output2572, pairMagnitude2542]

def corrSharedN02702MinusP016Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP016Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP016Output2572.1‖ ≤ (corrSharedN02702MinusP016Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP016BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP016Output2572,
    batchN02702MinusP016Center2558, batchN02702MinusP016Error2558, embedPair2542]

theorem corrSharedN02702MinusP016Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP016Output2572.1) + embedPair2542
            corrSharedN02702MinusP016Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP016Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP016Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP016Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP016Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP016Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP016Output2572, pairMagnitude2542]

def corrSharedN02702MinusP017Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP017Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP017Output2572.1‖ ≤ (corrSharedN02702MinusP017Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP017BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP017Output2572,
    batchN02702MinusP017Center2558, batchN02702MinusP017Error2558, embedPair2542]

theorem corrSharedN02702MinusP017Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP017Output2572.1) + embedPair2542
            corrSharedN02702MinusP017Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP017Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP017Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP017Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP017Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP017Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP017Output2572, pairMagnitude2542]

def corrSharedN02702MinusP018Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP018Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP018Output2572.1‖ ≤ (corrSharedN02702MinusP018Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP018BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP018Output2572,
    batchN02702MinusP018Center2558, batchN02702MinusP018Error2558, embedPair2542]

theorem corrSharedN02702MinusP018Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP018Output2572.1) + embedPair2542
            corrSharedN02702MinusP018Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP018Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP018Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP018Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP018Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP018Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP018Output2572, pairMagnitude2542]

def corrSharedN02702MinusP019Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP019Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP019Output2572.1‖ ≤ (corrSharedN02702MinusP019Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP019BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP019Output2572,
    batchN02702MinusP019Center2558, batchN02702MinusP019Error2558, embedPair2542]

theorem corrSharedN02702MinusP019Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP019Output2572.1) + embedPair2542
            corrSharedN02702MinusP019Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP019Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP019Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP019Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP019Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP019Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP019Output2572, pairMagnitude2542]

def corrSharedN02702MinusP020Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP020Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP020Output2572.1‖ ≤ (corrSharedN02702MinusP020Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP020BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP020Output2572,
    batchN02702MinusP020Center2558, batchN02702MinusP020Error2558, embedPair2542]

theorem corrSharedN02702MinusP020Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP020Output2572.1) + embedPair2542
            corrSharedN02702MinusP020Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP020Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP020Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP020Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP020Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP020Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP020Output2572, pairMagnitude2542]

def corrSharedN02702MinusP021Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP021Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP021Output2572.1‖ ≤ (corrSharedN02702MinusP021Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP021BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP021Output2572,
    batchN02702MinusP021Center2558, batchN02702MinusP021Error2558, embedPair2542]

theorem corrSharedN02702MinusP021Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP021Output2572.1) + embedPair2542
            corrSharedN02702MinusP021Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP021Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP021Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP021Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP021Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP021Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP021Output2572, pairMagnitude2542]

def corrSharedN02702MinusP022Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP022Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP022Output2572.1‖ ≤ (corrSharedN02702MinusP022Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP022BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP022Output2572,
    batchN02702MinusP022Center2558, batchN02702MinusP022Error2558, embedPair2542]

theorem corrSharedN02702MinusP022Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP022Output2572.1) + embedPair2542
            corrSharedN02702MinusP022Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP022Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP022Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP022Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP022Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP022Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP022Output2572, pairMagnitude2542]

def corrSharedN02702MinusP023Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP023Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP023Output2572.1‖ ≤ (corrSharedN02702MinusP023Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP023BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP023Output2572,
    batchN02702MinusP023Center2558, batchN02702MinusP023Error2558, embedPair2542]

theorem corrSharedN02702MinusP023Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP023Output2572.1) + embedPair2542
            corrSharedN02702MinusP023Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP023Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP023Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP023Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP023Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP023Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP023Output2572, pairMagnitude2542]

def corrSharedN02702MinusP024Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP024Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP024Output2572.1‖ ≤ (corrSharedN02702MinusP024Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP024BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP024Output2572,
    batchN02702MinusP024Center2558, batchN02702MinusP024Error2558, embedPair2542]

theorem corrSharedN02702MinusP024Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP024Output2572.1) + embedPair2542
            corrSharedN02702MinusP024Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP024Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP024Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP024Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP024Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP024Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP024Output2572, pairMagnitude2542]

def corrSharedN02702MinusP025Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP025Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP025Output2572.1‖ ≤ (corrSharedN02702MinusP025Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP025BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP025Output2572,
    batchN02702MinusP025Center2558, batchN02702MinusP025Error2558, embedPair2542]

theorem corrSharedN02702MinusP025Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP025Output2572.1) + embedPair2542
            corrSharedN02702MinusP025Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP025Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP025Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP025Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP025Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP025Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP025Output2572, pairMagnitude2542]

def corrSharedN02702MinusP026Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP026Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP026Output2572.1‖ ≤ (corrSharedN02702MinusP026Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP026BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP026Output2572,
    batchN02702MinusP026Center2558, batchN02702MinusP026Error2558, embedPair2542]

theorem corrSharedN02702MinusP026Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP026Output2572.1) + embedPair2542
            corrSharedN02702MinusP026Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP026Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP026Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP026Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP026Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP026Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP026Output2572, pairMagnitude2542]

def corrSharedN02702MinusP027Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP027Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP027Output2572.1‖ ≤ (corrSharedN02702MinusP027Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP027BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP027Output2572,
    batchN02702MinusP027Center2558, batchN02702MinusP027Error2558, embedPair2542]

theorem corrSharedN02702MinusP027Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP027Output2572.1) + embedPair2542
            corrSharedN02702MinusP027Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP027Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP027Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP027Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP027Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP027Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP027Output2572, pairMagnitude2542]

def corrSharedN02702MinusP028Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP028Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP028Output2572.1‖ ≤ (corrSharedN02702MinusP028Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP028BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP028Output2572,
    batchN02702MinusP028Center2558, batchN02702MinusP028Error2558, embedPair2542]

theorem corrSharedN02702MinusP028Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP028Output2572.1) + embedPair2542
            corrSharedN02702MinusP028Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP028Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP028Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP028Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP028Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP028Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP028Output2572, pairMagnitude2542]

def corrSharedN02702MinusP029Output2572 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem corrSharedN02702MinusP029Error2572 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP029Output2572.1‖ ≤ (corrSharedN02702MinusP029Output2572.2 : ℝ)
                := by
  have h := batchN02702MinusP029BaseError2558
  convert h using 1
  all_goals norm_num [corrSharedN02702MinusPosition2572, batchN02702MinusPosition2558,
      corrSharedN02702MinusP029Output2572,
    batchN02702MinusP029Center2558, batchN02702MinusP029Error2558, embedPair2542]

theorem corrSharedN02702MinusP029Norm2572 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02702MinusPosition2572‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP029Output2572.1) + embedPair2542
            corrSharedN02702MinusP029Output2572.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ corrSharedN02702MinusPosition2572 - embedPair2542
            corrSharedN02702MinusP029Output2572.1‖ + ‖embedPair2542
            corrSharedN02702MinusP029Output2572.1‖ := norm_add_le _ _
    _ ≤ (corrSharedN02702MinusP029Output2572.2 : ℝ) + (pairMagnitude2542
        corrSharedN02702MinusP029Output2572.1 : ℝ) :=
      add_le_add corrSharedN02702MinusP029Error2572 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [corrSharedN02702MinusP029Output2572, pairMagnitude2542]

noncomputable def corrSharedN02702MinusValue2572 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 corrSharedN02702MinusP000Output2572.1
  | 1 => embedPair2542 corrSharedN02702MinusP001Output2572.1
  | 2 => embedPair2542 corrSharedN02702MinusP002Output2572.1
  | 3 => embedPair2542 corrSharedN02702MinusP003Output2572.1
  | 4 => embedPair2542 corrSharedN02702MinusP004Output2572.1
  | 5 => embedPair2542 corrSharedN02702MinusP005Output2572.1
  | 6 => embedPair2542 corrSharedN02702MinusP006Output2572.1
  | 7 => embedPair2542 corrSharedN02702MinusP007Output2572.1
  | 8 => embedPair2542 corrSharedN02702MinusP008Output2572.1
  | 9 => embedPair2542 corrSharedN02702MinusP009Output2572.1
  | 10 => embedPair2542 corrSharedN02702MinusP010Output2572.1
  | 11 => embedPair2542 corrSharedN02702MinusP011Output2572.1
  | 12 => embedPair2542 corrSharedN02702MinusP012Output2572.1
  | 13 => embedPair2542 corrSharedN02702MinusP013Output2572.1
  | 14 => embedPair2542 corrSharedN02702MinusP014Output2572.1
  | 15 => embedPair2542 corrSharedN02702MinusP015Output2572.1
  | 16 => embedPair2542 corrSharedN02702MinusP016Output2572.1
  | 17 => embedPair2542 corrSharedN02702MinusP017Output2572.1
  | 18 => embedPair2542 corrSharedN02702MinusP018Output2572.1
  | 19 => embedPair2542 corrSharedN02702MinusP019Output2572.1
  | 20 => embedPair2542 corrSharedN02702MinusP020Output2572.1
  | 21 => embedPair2542 corrSharedN02702MinusP021Output2572.1
  | 22 => embedPair2542 corrSharedN02702MinusP022Output2572.1
  | 23 => embedPair2542 corrSharedN02702MinusP023Output2572.1
  | 24 => embedPair2542 corrSharedN02702MinusP024Output2572.1
  | 25 => embedPair2542 corrSharedN02702MinusP025Output2572.1
  | 26 => embedPair2542 corrSharedN02702MinusP026Output2572.1
  | 27 => embedPair2542 corrSharedN02702MinusP027Output2572.1
  | 28 => embedPair2542 corrSharedN02702MinusP028Output2572.1
  | 29 => embedPair2542 corrSharedN02702MinusP029Output2572.1
  | _ => 0

noncomputable def corrSharedN02702MinusError2572 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (corrSharedN02702MinusP000Output2572.2 : ℝ)
  | 1 => (corrSharedN02702MinusP001Output2572.2 : ℝ)
  | 2 => (corrSharedN02702MinusP002Output2572.2 : ℝ)
  | 3 => (corrSharedN02702MinusP003Output2572.2 : ℝ)
  | 4 => (corrSharedN02702MinusP004Output2572.2 : ℝ)
  | 5 => (corrSharedN02702MinusP005Output2572.2 : ℝ)
  | 6 => (corrSharedN02702MinusP006Output2572.2 : ℝ)
  | 7 => (corrSharedN02702MinusP007Output2572.2 : ℝ)
  | 8 => (corrSharedN02702MinusP008Output2572.2 : ℝ)
  | 9 => (corrSharedN02702MinusP009Output2572.2 : ℝ)
  | 10 => (corrSharedN02702MinusP010Output2572.2 : ℝ)
  | 11 => (corrSharedN02702MinusP011Output2572.2 : ℝ)
  | 12 => (corrSharedN02702MinusP012Output2572.2 : ℝ)
  | 13 => (corrSharedN02702MinusP013Output2572.2 : ℝ)
  | 14 => (corrSharedN02702MinusP014Output2572.2 : ℝ)
  | 15 => (corrSharedN02702MinusP015Output2572.2 : ℝ)
  | 16 => (corrSharedN02702MinusP016Output2572.2 : ℝ)
  | 17 => (corrSharedN02702MinusP017Output2572.2 : ℝ)
  | 18 => (corrSharedN02702MinusP018Output2572.2 : ℝ)
  | 19 => (corrSharedN02702MinusP019Output2572.2 : ℝ)
  | 20 => (corrSharedN02702MinusP020Output2572.2 : ℝ)
  | 21 => (corrSharedN02702MinusP021Output2572.2 : ℝ)
  | 22 => (corrSharedN02702MinusP022Output2572.2 : ℝ)
  | 23 => (corrSharedN02702MinusP023Output2572.2 : ℝ)
  | 24 => (corrSharedN02702MinusP024Output2572.2 : ℝ)
  | 25 => (corrSharedN02702MinusP025Output2572.2 : ℝ)
  | 26 => (corrSharedN02702MinusP026Output2572.2 : ℝ)
  | 27 => (corrSharedN02702MinusP027Output2572.2 : ℝ)
  | 28 => (corrSharedN02702MinusP028Output2572.2 : ℝ)
  | 29 => (corrSharedN02702MinusP029Output2572.2 : ℝ)
  | _ => 0

theorem corrSharedN02702MinusExp_error2572 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02702MinusPosition2572 -
            corrSharedN02702MinusValue2572 i‖
            ≤ corrSharedN02702MinusError2572 i := by
  fin_cases i
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP000Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP001Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP002Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP003Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP004Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP005Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP006Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP007Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP008Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP009Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP010Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP011Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP012Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP013Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP014Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP015Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP016Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP017Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP018Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP019Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP020Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP021Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP022Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP023Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP024Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP025Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP026Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP027Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP028Error2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP029Error2572

theorem corrSharedN02702MinusUnit_norm2572 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02702MinusPosition2572‖ ≤ 1 := by
  fin_cases i
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP000Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP001Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP002Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP003Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP004Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP005Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP006Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP007Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP008Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP009Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP010Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP011Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP012Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP013Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP014Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP015Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP016Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP017Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP018Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP019Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP020Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP021Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP022Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP023Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP024Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP025Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP026Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP027Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP028Norm2572
  · simpa only [corrSharedN02702MinusValue2572, corrSharedN02702MinusError2572] using
      corrSharedN02702MinusP029Norm2572

noncomputable def corrSharedN02702MinusSumValue2572 : ℂ := ⟨(((((18483836091013968823816672692 *
    10^40
        + 3068234172683732652471610903343032523223) * 10^40
        + 3319971902552509713933709321619969091434) * 10^40
        + 3378024967984822070705992695638309011465) : ℝ) /
        (((1636695303948070935006594848413 * 10^40
        + 7995761083210230215323947416456840480668) * 10^40
        + 9820233727744163504616295207857544334206) * 10^40
        + 3780035504608628272942696526664263794688)),
    (((-(((17586404768124732885957086488 * 10^40
        + 6821089276443553279748621886244000334529) * 10^40
        + 6641055427886177878427055910444987888742) * 10^40
        + 6746967323020968173967632778184081459935)) : ℝ) /
        (((1636695303948070935006594848413 * 10^40
        + 7995761083210230215323947416456840480668) * 10^40
        + 9820233727744163504616295207857544334206) * 10^40
        + 3780035504608628272942696526664263794688))⟩

noncomputable def corrSharedN02702MinusUpper2572 : ℝ := ((77941829 : ℝ) /
        5000000000)

theorem corrSharedN02702MinusSum_eq2572 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02702MinusValue2572 i) =
      corrSharedN02702MinusSumValue2572 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
        corrSharedN02702MinusValue2572,
      corrSharedN02702MinusSumValue2572, embedPair2542, corrSharedN02702MinusP000Output2572,
      corrSharedN02702MinusP001Output2572,
      corrSharedN02702MinusP002Output2572,
      corrSharedN02702MinusP003Output2572,
      corrSharedN02702MinusP004Output2572,
      corrSharedN02702MinusP005Output2572,
      corrSharedN02702MinusP006Output2572,
      corrSharedN02702MinusP007Output2572,
      corrSharedN02702MinusP008Output2572,
      corrSharedN02702MinusP009Output2572,
      corrSharedN02702MinusP010Output2572,
      corrSharedN02702MinusP011Output2572,
      corrSharedN02702MinusP012Output2572,
      corrSharedN02702MinusP013Output2572,
      corrSharedN02702MinusP014Output2572,
      corrSharedN02702MinusP015Output2572,
      corrSharedN02702MinusP016Output2572,
      corrSharedN02702MinusP017Output2572,
      corrSharedN02702MinusP018Output2572,
      corrSharedN02702MinusP019Output2572,
      corrSharedN02702MinusP020Output2572,
      corrSharedN02702MinusP021Output2572,
      corrSharedN02702MinusP022Output2572,
      corrSharedN02702MinusP023Output2572,
      corrSharedN02702MinusP024Output2572,
      corrSharedN02702MinusP025Output2572,
      corrSharedN02702MinusP026Output2572,
      corrSharedN02702MinusP027Output2572,
      corrSharedN02702MinusP028Output2572,
      corrSharedN02702MinusP029Output2572, Complex.mul_re, Complex.mul_im]

theorem corrSharedN02702MinusSum_norm2572 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02702MinusValue2572 i‖ ≤
      ((155883657 : ℝ) /
        10000000000) := by
  rw [corrSharedN02702MinusSum_eq2572]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [corrSharedN02702MinusSumValue2572]

theorem corrSharedN02702MinusEvaluation_charge2572 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * corrSharedN02702MinusError2572 i) ≤ (1 :
          ℝ)/10^12
          := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570,
      corrSharedN02702MinusError2572,
      corrSharedN02702MinusP000Output2572,
      corrSharedN02702MinusP001Output2572,
      corrSharedN02702MinusP002Output2572,
      corrSharedN02702MinusP003Output2572,
      corrSharedN02702MinusP004Output2572,
      corrSharedN02702MinusP005Output2572,
      corrSharedN02702MinusP006Output2572,
      corrSharedN02702MinusP007Output2572,
      corrSharedN02702MinusP008Output2572,
      corrSharedN02702MinusP009Output2572,
      corrSharedN02702MinusP010Output2572,
      corrSharedN02702MinusP011Output2572,
      corrSharedN02702MinusP012Output2572,
      corrSharedN02702MinusP013Output2572,
      corrSharedN02702MinusP014Output2572,
      corrSharedN02702MinusP015Output2572,
      corrSharedN02702MinusP016Output2572,
      corrSharedN02702MinusP017Output2572,
      corrSharedN02702MinusP018Output2572,
      corrSharedN02702MinusP019Output2572,
      corrSharedN02702MinusP020Output2572,
      corrSharedN02702MinusP021Output2572,
      corrSharedN02702MinusP022Output2572,
      corrSharedN02702MinusP023Output2572,
      corrSharedN02702MinusP024Output2572,
      corrSharedN02702MinusP025Output2572,
      corrSharedN02702MinusP026Output2572,
      corrSharedN02702MinusP027Output2572,
      corrSharedN02702MinusP028Output2572,
      corrSharedN02702MinusP029Output2572]

theorem corrSharedN02702MinusSigned_le2572 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 corrSharedN02702MinusPosition2572 ≤ corrSharedN02702MinusUpper2572 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02702MinusPosition2572‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * corrSharedN02702MinusValue2572 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * corrSharedN02702MinusError2572 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (corrSharedN02702MinusExp_error2572 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02702MinusPosition2572‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (corrSharedN02702MinusUnit_norm2572 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i corrSharedN02702MinusPosition2572‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 corrSharedN02702MinusUpper2572
  linarith [corrSharedN02702MinusSum_norm2572, corrSharedN02702MinusEvaluation_charge2572]

theorem corrSharedN02702MinusPhysical_le2572 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 corrSharedN02702MinusPosition2572‖ ≤
      corrSharedN02702MinusUpper2572 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        corrSharedN02702MinusPosition2572
  simpa only [iteratedDeriv_zero] using h.trans corrSharedN02702MinusSigned_le2572

theorem corrSharedN02702MinusGrid2572 :
    -stripRadius2303 + (2702 : ℝ)*(2*stripRadius2303/10240) = corrSharedN02702MinusPosition2572 :=
        by
  norm_num [stripRadius2303, corrSharedN02702MinusPosition2572]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.corrSharedN02702MinusSigned_le2572
#print axioms ConnesWeilRH.Dev.corrSharedN02702MinusPhysical_le2572
