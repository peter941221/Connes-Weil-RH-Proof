import ConnesWeilRH.Dev.C1RouteABatchN02705Plus2654
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchValueN02705PlusPosition2654 : ℝ := (((-31653888483) : ℝ) /
        10240000000)

def batchValueN02705PlusP000Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem batchValueN02705PlusP000Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP000Output2654.1‖ ≤ (batchValueN02705PlusP000Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP000BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP000Output2654,
    batchN02705PlusP000Center2654, batchN02705PlusP000Error2654, embedPair2542]

theorem batchValueN02705PlusP000Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP000Output2654.1) + embedPair2542
            batchValueN02705PlusP000Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP000Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP000Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP000Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP000Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP000Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP000Output2654, pairMagnitude2542]

def batchValueN02705PlusP001Output2654 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP001Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP001Output2654.1‖ ≤ (batchValueN02705PlusP001Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP001BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP001Output2654,
    batchN02705PlusP001Center2654, batchN02705PlusP001Error2654, embedPair2542]

theorem batchValueN02705PlusP001Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP001Output2654.1) + embedPair2542
            batchValueN02705PlusP001Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP001Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP001Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP001Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP001Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP001Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP001Output2654, pairMagnitude2542]

def batchValueN02705PlusP002Output2654 : RatState2542 :=
  (((((-283269467081739495401) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-697336509513847197747) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((715960097493195589 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN02705PlusP002Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP002Output2654.1‖ ≤ (batchValueN02705PlusP002Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP002BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP002Output2654,
    batchN02705PlusP002Center2654, batchN02705PlusP002Error2654, embedPair2542]

theorem batchValueN02705PlusP002Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP002Output2654.1) + embedPair2542
            batchValueN02705PlusP002Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP002Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP002Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP002Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP002Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP002Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP002Output2654, pairMagnitude2542]

def batchValueN02705PlusP003Output2654 : RatState2542 :=
  (((((-2122071398865999455084083525) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-10447987052535926618002489217) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((40226203768278363825291287 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP003Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP003Output2654.1‖ ≤ (batchValueN02705PlusP003Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP003BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP003Output2654,
    batchN02705PlusP003Center2654, batchN02705PlusP003Error2654, embedPair2542]

theorem batchValueN02705PlusP003Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP003Output2654.1) + embedPair2542
            batchValueN02705PlusP003Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP003Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP003Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP003Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP003Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP003Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP003Output2654, pairMagnitude2542]

def batchValueN02705PlusP004Output2654 : RatState2542 :=
  (((((-2052089403884525222829097911721) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((2525857934597415579677892312545 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((4746455199159367328887253045 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN02705PlusP004Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP004Output2654.1‖ ≤ (batchValueN02705PlusP004Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP004BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP004Output2654,
    batchN02705PlusP004Center2654, batchN02705PlusP004Error2654, embedPair2542]

theorem batchValueN02705PlusP004Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP004Output2654.1) + embedPair2542
            batchValueN02705PlusP004Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP004Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP004Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP004Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP004Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP004Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP004Output2654, pairMagnitude2542]

def batchValueN02705PlusP005Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem batchValueN02705PlusP005Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP005Output2654.1‖ ≤ (batchValueN02705PlusP005Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP005BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP005Output2654,
    batchN02705PlusP005Center2654, batchN02705PlusP005Error2654, embedPair2542]

theorem batchValueN02705PlusP005Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP005Output2654.1) + embedPair2542
            batchValueN02705PlusP005Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP005Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP005Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP005Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP005Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP005Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP005Output2654, pairMagnitude2542]

def batchValueN02705PlusP006Output2654 : RatState2542 :=
  ((((700265187724743 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((1278008009571 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN02705PlusP006Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP006Output2654.1‖ ≤ (batchValueN02705PlusP006Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP006BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP006Output2654,
    batchN02705PlusP006Center2654, batchN02705PlusP006Error2654, embedPair2542]

theorem batchValueN02705PlusP006Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP006Output2654.1) + embedPair2542
            batchValueN02705PlusP006Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP006Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP006Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP006Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP006Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP006Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP006Output2654, pairMagnitude2542]

def batchValueN02705PlusP007Output2654 : RatState2542 :=
  ((((11277108740164686308975014741 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((409050545734292758920081 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN02705PlusP007Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP007Output2654.1‖ ≤ (batchValueN02705PlusP007Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP007BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP007Output2654,
    batchN02705PlusP007Center2654, batchN02705PlusP007Error2654, embedPair2542]

theorem batchValueN02705PlusP007Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP007Output2654.1) + embedPair2542
            batchValueN02705PlusP007Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP007Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP007Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP007Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP007Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP007Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP007Output2654, pairMagnitude2542]

def batchValueN02705PlusP008Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP008Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP008Output2654.1‖ ≤ (batchValueN02705PlusP008Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP008BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP008Output2654,
    batchN02705PlusP008Center2654, batchN02705PlusP008Error2654, embedPair2542]

theorem batchValueN02705PlusP008Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP008Output2654.1) + embedPair2542
            batchValueN02705PlusP008Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP008Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP008Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP008Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP008Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP008Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP008Output2654, pairMagnitude2542]

def batchValueN02705PlusP009Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP009Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP009Output2654.1‖ ≤ (batchValueN02705PlusP009Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP009BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP009Output2654,
    batchN02705PlusP009Center2654, batchN02705PlusP009Error2654, embedPair2542]

theorem batchValueN02705PlusP009Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP009Output2654.1) + embedPair2542
            batchValueN02705PlusP009Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP009Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP009Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP009Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP009Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP009Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP009Output2654, pairMagnitude2542]

def batchValueN02705PlusP010Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP010Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP010Output2654.1‖ ≤ (batchValueN02705PlusP010Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP010BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP010Output2654,
    batchN02705PlusP010Center2654, batchN02705PlusP010Error2654, embedPair2542]

theorem batchValueN02705PlusP010Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP010Output2654.1) + embedPair2542
            batchValueN02705PlusP010Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP010Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP010Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP010Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP010Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP010Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP010Output2654, pairMagnitude2542]

def batchValueN02705PlusP011Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP011Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP011Output2654.1‖ ≤ (batchValueN02705PlusP011Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP011BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP011Output2654,
    batchN02705PlusP011Center2654, batchN02705PlusP011Error2654, embedPair2542]

theorem batchValueN02705PlusP011Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP011Output2654.1) + embedPair2542
            batchValueN02705PlusP011Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP011Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP011Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP011Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP011Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP011Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP011Output2654, pairMagnitude2542]

def batchValueN02705PlusP012Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP012Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP012Output2654.1‖ ≤ (batchValueN02705PlusP012Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP012BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP012Output2654,
    batchN02705PlusP012Center2654, batchN02705PlusP012Error2654, embedPair2542]

theorem batchValueN02705PlusP012Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP012Output2654.1) + embedPair2542
            batchValueN02705PlusP012Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP012Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP012Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP012Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP012Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP012Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP012Output2654, pairMagnitude2542]

def batchValueN02705PlusP013Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP013Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP013Output2654.1‖ ≤ (batchValueN02705PlusP013Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP013BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP013Output2654,
    batchN02705PlusP013Center2654, batchN02705PlusP013Error2654, embedPair2542]

theorem batchValueN02705PlusP013Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP013Output2654.1) + embedPair2542
            batchValueN02705PlusP013Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP013Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP013Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP013Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP013Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP013Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP013Output2654, pairMagnitude2542]

def batchValueN02705PlusP014Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP014Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP014Output2654.1‖ ≤ (batchValueN02705PlusP014Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP014BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP014Output2654,
    batchN02705PlusP014Center2654, batchN02705PlusP014Error2654, embedPair2542]

theorem batchValueN02705PlusP014Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP014Output2654.1) + embedPair2542
            batchValueN02705PlusP014Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP014Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP014Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP014Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP014Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP014Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP014Output2654, pairMagnitude2542]

def batchValueN02705PlusP015Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP015Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP015Output2654.1‖ ≤ (batchValueN02705PlusP015Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP015BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP015Output2654,
    batchN02705PlusP015Center2654, batchN02705PlusP015Error2654, embedPair2542]

theorem batchValueN02705PlusP015Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP015Output2654.1) + embedPair2542
            batchValueN02705PlusP015Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP015Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP015Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP015Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP015Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP015Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP015Output2654, pairMagnitude2542]

def batchValueN02705PlusP016Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP016Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP016Output2654.1‖ ≤ (batchValueN02705PlusP016Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP016BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP016Output2654,
    batchN02705PlusP016Center2654, batchN02705PlusP016Error2654, embedPair2542]

theorem batchValueN02705PlusP016Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP016Output2654.1) + embedPair2542
            batchValueN02705PlusP016Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP016Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP016Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP016Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP016Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP016Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP016Output2654, pairMagnitude2542]

def batchValueN02705PlusP017Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP017Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP017Output2654.1‖ ≤ (batchValueN02705PlusP017Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP017BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP017Output2654,
    batchN02705PlusP017Center2654, batchN02705PlusP017Error2654, embedPair2542]

theorem batchValueN02705PlusP017Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP017Output2654.1) + embedPair2542
            batchValueN02705PlusP017Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP017Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP017Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP017Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP017Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP017Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP017Output2654, pairMagnitude2542]

def batchValueN02705PlusP018Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP018Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP018Output2654.1‖ ≤ (batchValueN02705PlusP018Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP018BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP018Output2654,
    batchN02705PlusP018Center2654, batchN02705PlusP018Error2654, embedPair2542]

theorem batchValueN02705PlusP018Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP018Output2654.1) + embedPair2542
            batchValueN02705PlusP018Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP018Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP018Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP018Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP018Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP018Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP018Output2654, pairMagnitude2542]

def batchValueN02705PlusP019Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP019Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP019Output2654.1‖ ≤ (batchValueN02705PlusP019Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP019BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP019Output2654,
    batchN02705PlusP019Center2654, batchN02705PlusP019Error2654, embedPair2542]

theorem batchValueN02705PlusP019Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP019Output2654.1) + embedPair2542
            batchValueN02705PlusP019Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP019Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP019Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP019Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP019Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP019Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP019Output2654, pairMagnitude2542]

def batchValueN02705PlusP020Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP020Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP020Output2654.1‖ ≤ (batchValueN02705PlusP020Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP020BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP020Output2654,
    batchN02705PlusP020Center2654, batchN02705PlusP020Error2654, embedPair2542]

theorem batchValueN02705PlusP020Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP020Output2654.1) + embedPair2542
            batchValueN02705PlusP020Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP020Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP020Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP020Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP020Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP020Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP020Output2654, pairMagnitude2542]

def batchValueN02705PlusP021Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP021Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP021Output2654.1‖ ≤ (batchValueN02705PlusP021Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP021BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP021Output2654,
    batchN02705PlusP021Center2654, batchN02705PlusP021Error2654, embedPair2542]

theorem batchValueN02705PlusP021Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP021Output2654.1) + embedPair2542
            batchValueN02705PlusP021Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP021Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP021Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP021Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP021Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP021Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP021Output2654, pairMagnitude2542]

def batchValueN02705PlusP022Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP022Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP022Output2654.1‖ ≤ (batchValueN02705PlusP022Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP022BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP022Output2654,
    batchN02705PlusP022Center2654, batchN02705PlusP022Error2654, embedPair2542]

theorem batchValueN02705PlusP022Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP022Output2654.1) + embedPair2542
            batchValueN02705PlusP022Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP022Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP022Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP022Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP022Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP022Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP022Output2654, pairMagnitude2542]

def batchValueN02705PlusP023Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP023Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP023Output2654.1‖ ≤ (batchValueN02705PlusP023Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP023BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP023Output2654,
    batchN02705PlusP023Center2654, batchN02705PlusP023Error2654, embedPair2542]

theorem batchValueN02705PlusP023Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP023Output2654.1) + embedPair2542
            batchValueN02705PlusP023Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP023Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP023Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP023Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP023Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP023Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP023Output2654, pairMagnitude2542]

def batchValueN02705PlusP024Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP024Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP024Output2654.1‖ ≤ (batchValueN02705PlusP024Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP024BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP024Output2654,
    batchN02705PlusP024Center2654, batchN02705PlusP024Error2654, embedPair2542]

theorem batchValueN02705PlusP024Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP024Output2654.1) + embedPair2542
            batchValueN02705PlusP024Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP024Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP024Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP024Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP024Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP024Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP024Output2654, pairMagnitude2542]

def batchValueN02705PlusP025Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP025Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP025Output2654.1‖ ≤ (batchValueN02705PlusP025Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP025BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP025Output2654,
    batchN02705PlusP025Center2654, batchN02705PlusP025Error2654, embedPair2542]

theorem batchValueN02705PlusP025Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP025Output2654.1) + embedPair2542
            batchValueN02705PlusP025Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP025Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP025Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP025Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP025Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP025Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP025Output2654, pairMagnitude2542]

def batchValueN02705PlusP026Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP026Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP026Output2654.1‖ ≤ (batchValueN02705PlusP026Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP026BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP026Output2654,
    batchN02705PlusP026Center2654, batchN02705PlusP026Error2654, embedPair2542]

theorem batchValueN02705PlusP026Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP026Output2654.1) + embedPair2542
            batchValueN02705PlusP026Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP026Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP026Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP026Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP026Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP026Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP026Output2654, pairMagnitude2542]

def batchValueN02705PlusP027Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP027Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP027Output2654.1‖ ≤ (batchValueN02705PlusP027Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP027BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP027Output2654,
    batchN02705PlusP027Center2654, batchN02705PlusP027Error2654, embedPair2542]

theorem batchValueN02705PlusP027Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP027Output2654.1) + embedPair2542
            batchValueN02705PlusP027Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP027Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP027Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP027Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP027Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP027Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP027Output2654, pairMagnitude2542]

def batchValueN02705PlusP028Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP028Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP028Output2654.1‖ ≤ (batchValueN02705PlusP028Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP028BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP028Output2654,
    batchN02705PlusP028Center2654, batchN02705PlusP028Error2654, embedPair2542]

theorem batchValueN02705PlusP028Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP028Output2654.1) + embedPair2542
            batchValueN02705PlusP028Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP028Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP028Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP028Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP028Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP028Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP028Output2654, pairMagnitude2542]

def batchValueN02705PlusP029Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705PlusP029Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP029Output2654.1‖ ≤ (batchValueN02705PlusP029Output2654.2 : ℝ) :=
                by
  have h := batchN02705PlusP029BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705PlusPosition2654, batchN02705PlusPosition2654,
      batchValueN02705PlusP029Output2654,
    batchN02705PlusP029Center2654, batchN02705PlusP029Error2654, embedPair2542]

theorem batchValueN02705PlusP029Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02705PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02705PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP029Output2654.1) + embedPair2542
            batchValueN02705PlusP029Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02705PlusPosition2654 - embedPair2542
            batchValueN02705PlusP029Output2654.1‖ + ‖embedPair2542
            batchValueN02705PlusP029Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705PlusP029Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705PlusP029Output2654.1 : ℝ) :=
      add_le_add batchValueN02705PlusP029Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705PlusP029Output2654, pairMagnitude2542]

noncomputable def batchValueN02705PlusValue2654 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchValueN02705PlusP000Output2654.1
  | 1 => embedPair2542 batchValueN02705PlusP001Output2654.1
  | 2 => embedPair2542 batchValueN02705PlusP002Output2654.1
  | 3 => embedPair2542 batchValueN02705PlusP003Output2654.1
  | 4 => embedPair2542 batchValueN02705PlusP004Output2654.1
  | 5 => embedPair2542 batchValueN02705PlusP005Output2654.1
  | 6 => embedPair2542 batchValueN02705PlusP006Output2654.1
  | 7 => embedPair2542 batchValueN02705PlusP007Output2654.1
  | 8 => embedPair2542 batchValueN02705PlusP008Output2654.1
  | 9 => embedPair2542 batchValueN02705PlusP009Output2654.1
  | 10 => embedPair2542 batchValueN02705PlusP010Output2654.1
  | 11 => embedPair2542 batchValueN02705PlusP011Output2654.1
  | 12 => embedPair2542 batchValueN02705PlusP012Output2654.1
  | 13 => embedPair2542 batchValueN02705PlusP013Output2654.1
  | 14 => embedPair2542 batchValueN02705PlusP014Output2654.1
  | 15 => embedPair2542 batchValueN02705PlusP015Output2654.1
  | 16 => embedPair2542 batchValueN02705PlusP016Output2654.1
  | 17 => embedPair2542 batchValueN02705PlusP017Output2654.1
  | 18 => embedPair2542 batchValueN02705PlusP018Output2654.1
  | 19 => embedPair2542 batchValueN02705PlusP019Output2654.1
  | 20 => embedPair2542 batchValueN02705PlusP020Output2654.1
  | 21 => embedPair2542 batchValueN02705PlusP021Output2654.1
  | 22 => embedPair2542 batchValueN02705PlusP022Output2654.1
  | 23 => embedPair2542 batchValueN02705PlusP023Output2654.1
  | 24 => embedPair2542 batchValueN02705PlusP024Output2654.1
  | 25 => embedPair2542 batchValueN02705PlusP025Output2654.1
  | 26 => embedPair2542 batchValueN02705PlusP026Output2654.1
  | 27 => embedPair2542 batchValueN02705PlusP027Output2654.1
  | 28 => embedPair2542 batchValueN02705PlusP028Output2654.1
  | 29 => embedPair2542 batchValueN02705PlusP029Output2654.1
  | _ => 0

noncomputable def batchValueN02705PlusError2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (batchValueN02705PlusP000Output2654.2 : ℝ)
  | 1 => (batchValueN02705PlusP001Output2654.2 : ℝ)
  | 2 => (batchValueN02705PlusP002Output2654.2 : ℝ)
  | 3 => (batchValueN02705PlusP003Output2654.2 : ℝ)
  | 4 => (batchValueN02705PlusP004Output2654.2 : ℝ)
  | 5 => (batchValueN02705PlusP005Output2654.2 : ℝ)
  | 6 => (batchValueN02705PlusP006Output2654.2 : ℝ)
  | 7 => (batchValueN02705PlusP007Output2654.2 : ℝ)
  | 8 => (batchValueN02705PlusP008Output2654.2 : ℝ)
  | 9 => (batchValueN02705PlusP009Output2654.2 : ℝ)
  | 10 => (batchValueN02705PlusP010Output2654.2 : ℝ)
  | 11 => (batchValueN02705PlusP011Output2654.2 : ℝ)
  | 12 => (batchValueN02705PlusP012Output2654.2 : ℝ)
  | 13 => (batchValueN02705PlusP013Output2654.2 : ℝ)
  | 14 => (batchValueN02705PlusP014Output2654.2 : ℝ)
  | 15 => (batchValueN02705PlusP015Output2654.2 : ℝ)
  | 16 => (batchValueN02705PlusP016Output2654.2 : ℝ)
  | 17 => (batchValueN02705PlusP017Output2654.2 : ℝ)
  | 18 => (batchValueN02705PlusP018Output2654.2 : ℝ)
  | 19 => (batchValueN02705PlusP019Output2654.2 : ℝ)
  | 20 => (batchValueN02705PlusP020Output2654.2 : ℝ)
  | 21 => (batchValueN02705PlusP021Output2654.2 : ℝ)
  | 22 => (batchValueN02705PlusP022Output2654.2 : ℝ)
  | 23 => (batchValueN02705PlusP023Output2654.2 : ℝ)
  | 24 => (batchValueN02705PlusP024Output2654.2 : ℝ)
  | 25 => (batchValueN02705PlusP025Output2654.2 : ℝ)
  | 26 => (batchValueN02705PlusP026Output2654.2 : ℝ)
  | 27 => (batchValueN02705PlusP027Output2654.2 : ℝ)
  | 28 => (batchValueN02705PlusP028Output2654.2 : ℝ)
  | 29 => (batchValueN02705PlusP029Output2654.2 : ℝ)
  | _ => 0

theorem batchValueN02705PlusExp_error2654 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02705PlusPosition2654 - batchValueN02705PlusValue2654
            i‖ ≤
            batchValueN02705PlusError2654 i := by
  fin_cases i
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP000Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP001Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP002Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP003Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP004Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP005Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP006Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP007Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP008Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP009Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP010Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP011Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP012Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP013Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP014Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP015Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP016Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP017Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP018Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP019Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP020Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP021Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP022Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP023Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP024Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP025Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP026Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP027Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP028Error2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP029Error2654

theorem batchValueN02705PlusUnit_norm2654 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02705PlusPosition2654‖ ≤ 1 := by
  fin_cases i
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP000Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP001Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP002Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP003Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP004Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP005Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP006Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP007Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP008Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP009Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP010Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP011Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP012Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP013Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP014Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP015Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP016Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP017Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP018Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP019Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP020Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP021Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP022Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP023Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP024Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP025Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP026Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP027Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP028Norm2654
  · simpa only [batchValueN02705PlusValue2654, batchValueN02705PlusError2654] using
      batchValueN02705PlusP029Norm2654

noncomputable def batchValueN02705PlusSumValue2654 : ℂ := ⟨(((((3257557160305389885 * 10^40
        + 1960600215967822209274838601843425861102) * 10^40
        + 2502689938760447698494283645254736392744) * 10^40
        + 392866381475410777022610249510642707405) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816)),
    (((((2020203988197685168 * 10^40
        + 1191126039871737741400380241145282052423) * 10^40
        + 7225800786261211053814310629842588978922) * 10^40
        + 4283648488208486468769374738293917438949) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816))⟩

noncomputable def batchValueN02705PlusUpper2654 : ℝ := ((769 : ℝ) /
        10000000000)

theorem batchValueN02705PlusSum_eq2654 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02705PlusValue2654 i) =
      batchValueN02705PlusSumValue2654 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN02705PlusValue2654,
      batchValueN02705PlusSumValue2654, embedPair2542, batchValueN02705PlusP000Output2654,
      batchValueN02705PlusP001Output2654,
      batchValueN02705PlusP002Output2654,
      batchValueN02705PlusP003Output2654,
      batchValueN02705PlusP004Output2654,
      batchValueN02705PlusP005Output2654,
      batchValueN02705PlusP006Output2654,
      batchValueN02705PlusP007Output2654,
      batchValueN02705PlusP008Output2654,
      batchValueN02705PlusP009Output2654,
      batchValueN02705PlusP010Output2654,
      batchValueN02705PlusP011Output2654,
      batchValueN02705PlusP012Output2654,
      batchValueN02705PlusP013Output2654,
      batchValueN02705PlusP014Output2654,
      batchValueN02705PlusP015Output2654,
      batchValueN02705PlusP016Output2654,
      batchValueN02705PlusP017Output2654,
      batchValueN02705PlusP018Output2654,
      batchValueN02705PlusP019Output2654,
      batchValueN02705PlusP020Output2654,
      batchValueN02705PlusP021Output2654,
      batchValueN02705PlusP022Output2654,
      batchValueN02705PlusP023Output2654,
      batchValueN02705PlusP024Output2654,
      batchValueN02705PlusP025Output2654,
      batchValueN02705PlusP026Output2654,
      batchValueN02705PlusP027Output2654,
      batchValueN02705PlusP028Output2654,
      batchValueN02705PlusP029Output2654, Complex.mul_re, Complex.mul_im]

theorem batchValueN02705PlusSum_norm2654 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02705PlusValue2654 i‖ ≤
      ((3 : ℝ) /
        39062500) := by
  rw [batchValueN02705PlusSum_eq2654]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchValueN02705PlusSumValue2654]

theorem batchValueN02705PlusEvaluation_charge2654 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchValueN02705PlusError2654 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN02705PlusError2654,
      batchValueN02705PlusP000Output2654,
      batchValueN02705PlusP001Output2654,
      batchValueN02705PlusP002Output2654,
      batchValueN02705PlusP003Output2654,
      batchValueN02705PlusP004Output2654,
      batchValueN02705PlusP005Output2654,
      batchValueN02705PlusP006Output2654,
      batchValueN02705PlusP007Output2654,
      batchValueN02705PlusP008Output2654,
      batchValueN02705PlusP009Output2654,
      batchValueN02705PlusP010Output2654,
      batchValueN02705PlusP011Output2654,
      batchValueN02705PlusP012Output2654,
      batchValueN02705PlusP013Output2654,
      batchValueN02705PlusP014Output2654,
      batchValueN02705PlusP015Output2654,
      batchValueN02705PlusP016Output2654,
      batchValueN02705PlusP017Output2654,
      batchValueN02705PlusP018Output2654,
      batchValueN02705PlusP019Output2654,
      batchValueN02705PlusP020Output2654,
      batchValueN02705PlusP021Output2654,
      batchValueN02705PlusP022Output2654,
      batchValueN02705PlusP023Output2654,
      batchValueN02705PlusP024Output2654,
      batchValueN02705PlusP025Output2654,
      batchValueN02705PlusP026Output2654,
      batchValueN02705PlusP027Output2654,
      batchValueN02705PlusP028Output2654,
      batchValueN02705PlusP029Output2654]

theorem batchValueN02705PlusSigned_le2654 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchValueN02705PlusPosition2654 ≤ batchValueN02705PlusUpper2654 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02705PlusPosition2654‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02705PlusValue2654 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchValueN02705PlusError2654 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (batchValueN02705PlusExp_error2654 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02705PlusPosition2654‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchValueN02705PlusUnit_norm2654 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02705PlusPosition2654‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchValueN02705PlusUpper2654
  linarith [batchValueN02705PlusSum_norm2654, batchValueN02705PlusEvaluation_charge2654]

theorem batchValueN02705PlusPhysical_le2654 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 batchValueN02705PlusPosition2654‖ ≤
      batchValueN02705PlusUpper2654 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchValueN02705PlusPosition2654
  simpa only [iteratedDeriv_zero] using h.trans batchValueN02705PlusSigned_le2654

theorem batchValueN02705PlusGrid2654 :
    -stripRadius2303 + (2705 : ℝ)*(2*stripRadius2303/10240) = batchValueN02705PlusPosition2654 :=
        by
  norm_num [stripRadius2303, batchValueN02705PlusPosition2654]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchValueN02705PlusSigned_le2654
#print axioms ConnesWeilRH.Dev.batchValueN02705PlusPhysical_le2654
