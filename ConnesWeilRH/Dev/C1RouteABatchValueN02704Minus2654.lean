import ConnesWeilRH.Dev.C1RouteABatchN02704Minus2654
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchValueN02704MinusPosition2654 : ℝ := (((-9895936151) : ℝ) /
        3200000000)

def batchValueN02704MinusP000Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem batchValueN02704MinusP000Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP000Output2654.1‖ ≤ (batchValueN02704MinusP000Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP000BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP000Output2654,
    batchN02704MinusP000Center2654, batchN02704MinusP000Error2654, embedPair2542]

theorem batchValueN02704MinusP000Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP000Output2654.1) + embedPair2542
            batchValueN02704MinusP000Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP000Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP000Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP000Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP000Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP000Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP000Output2654, pairMagnitude2542]

def batchValueN02704MinusP001Output2654 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP001Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP001Output2654.1‖ ≤ (batchValueN02704MinusP001Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP001BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP001Output2654,
    batchN02704MinusP001Center2654, batchN02704MinusP001Error2654, embedPair2542]

theorem batchValueN02704MinusP001Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP001Output2654.1) + embedPair2542
            batchValueN02704MinusP001Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP001Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP001Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP001Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP001Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP001Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP001Output2654, pairMagnitude2542]

def batchValueN02704MinusP002Output2654 : RatState2542 :=
  (((((-1659707957179232547945) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-14245775921432001046225) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((14710856534966248467 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN02704MinusP002Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP002Output2654.1‖ ≤ (batchValueN02704MinusP002Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP002BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP002Output2654,
    batchN02704MinusP002Center2654, batchN02704MinusP002Error2654, embedPair2542]

theorem batchValueN02704MinusP002Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP002Output2654.1) + embedPair2542
            batchValueN02704MinusP002Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP002Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP002Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP002Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP002Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP002Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP002Output2654, pairMagnitude2542]

def batchValueN02704MinusP003Output2654 : RatState2542 :=
  (((((-102983243484972695843730390395) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-220984090002582734303232415591) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((53476660314846633286429113 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336)))

theorem batchValueN02704MinusP003Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP003Output2654.1‖ ≤ (batchValueN02704MinusP003Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP003BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP003Output2654,
    batchN02704MinusP003Center2654, batchN02704MinusP003Error2654, embedPair2542]

theorem batchValueN02704MinusP003Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP003Output2654.1) + embedPair2542
            batchValueN02704MinusP003Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP003Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP003Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP003Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP003Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP003Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP003Output2654, pairMagnitude2542]

def batchValueN02704MinusP004Output2654 : RatState2542 :=
  (((((-50249225686456146115974385225945) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((26956519905289865112084360768053 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((203758462513469541571904517823 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN02704MinusP004Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP004Output2654.1‖ ≤ (batchValueN02704MinusP004Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP004BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP004Output2654,
    batchN02704MinusP004Center2654, batchN02704MinusP004Error2654, embedPair2542]

theorem batchValueN02704MinusP004Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP004Output2654.1) + embedPair2542
            batchValueN02704MinusP004Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP004Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP004Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP004Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP004Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP004Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP004Output2654, pairMagnitude2542]

def batchValueN02704MinusP005Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem batchValueN02704MinusP005Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP005Output2654.1‖ ≤ (batchValueN02704MinusP005Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP005BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP005Output2654,
    batchN02704MinusP005Center2654, batchN02704MinusP005Error2654, embedPair2542]

theorem batchValueN02704MinusP005Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP005Output2654.1) + embedPair2542
            batchValueN02704MinusP005Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP005Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP005Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP005Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP005Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP005Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP005Output2654, pairMagnitude2542]

def batchValueN02704MinusP006Output2654 : RatState2542 :=
  ((((14068696455048369 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((2301259777463 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN02704MinusP006Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP006Output2654.1‖ ≤ (batchValueN02704MinusP006Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP006BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP006Output2654,
    batchN02704MinusP006Center2654, batchN02704MinusP006Error2654, embedPair2542]

theorem batchValueN02704MinusP006Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP006Output2654.1) + embedPair2542
            batchValueN02704MinusP006Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP006Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP006Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP006Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP006Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP006Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP006Output2654, pairMagnitude2542]

def batchValueN02704MinusP007Output2654 : RatState2542 :=
  ((((121901103843397125307301253425 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((8428687828913767722721185 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN02704MinusP007Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP007Output2654.1‖ ≤ (batchValueN02704MinusP007Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP007BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP007Output2654,
    batchN02704MinusP007Center2654, batchN02704MinusP007Error2654, embedPair2542]

theorem batchValueN02704MinusP007Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP007Output2654.1) + embedPair2542
            batchValueN02704MinusP007Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP007Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP007Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP007Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP007Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP007Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP007Output2654, pairMagnitude2542]

def batchValueN02704MinusP008Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP008Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP008Output2654.1‖ ≤ (batchValueN02704MinusP008Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP008BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP008Output2654,
    batchN02704MinusP008Center2654, batchN02704MinusP008Error2654, embedPair2542]

theorem batchValueN02704MinusP008Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP008Output2654.1) + embedPair2542
            batchValueN02704MinusP008Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP008Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP008Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP008Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP008Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP008Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP008Output2654, pairMagnitude2542]

def batchValueN02704MinusP009Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP009Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP009Output2654.1‖ ≤ (batchValueN02704MinusP009Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP009BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP009Output2654,
    batchN02704MinusP009Center2654, batchN02704MinusP009Error2654, embedPair2542]

theorem batchValueN02704MinusP009Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP009Output2654.1) + embedPair2542
            batchValueN02704MinusP009Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP009Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP009Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP009Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP009Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP009Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP009Output2654, pairMagnitude2542]

def batchValueN02704MinusP010Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP010Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP010Output2654.1‖ ≤ (batchValueN02704MinusP010Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP010BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP010Output2654,
    batchN02704MinusP010Center2654, batchN02704MinusP010Error2654, embedPair2542]

theorem batchValueN02704MinusP010Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP010Output2654.1) + embedPair2542
            batchValueN02704MinusP010Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP010Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP010Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP010Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP010Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP010Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP010Output2654, pairMagnitude2542]

def batchValueN02704MinusP011Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP011Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP011Output2654.1‖ ≤ (batchValueN02704MinusP011Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP011BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP011Output2654,
    batchN02704MinusP011Center2654, batchN02704MinusP011Error2654, embedPair2542]

theorem batchValueN02704MinusP011Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP011Output2654.1) + embedPair2542
            batchValueN02704MinusP011Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP011Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP011Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP011Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP011Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP011Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP011Output2654, pairMagnitude2542]

def batchValueN02704MinusP012Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP012Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP012Output2654.1‖ ≤ (batchValueN02704MinusP012Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP012BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP012Output2654,
    batchN02704MinusP012Center2654, batchN02704MinusP012Error2654, embedPair2542]

theorem batchValueN02704MinusP012Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP012Output2654.1) + embedPair2542
            batchValueN02704MinusP012Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP012Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP012Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP012Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP012Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP012Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP012Output2654, pairMagnitude2542]

def batchValueN02704MinusP013Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP013Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP013Output2654.1‖ ≤ (batchValueN02704MinusP013Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP013BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP013Output2654,
    batchN02704MinusP013Center2654, batchN02704MinusP013Error2654, embedPair2542]

theorem batchValueN02704MinusP013Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP013Output2654.1) + embedPair2542
            batchValueN02704MinusP013Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP013Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP013Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP013Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP013Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP013Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP013Output2654, pairMagnitude2542]

def batchValueN02704MinusP014Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP014Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP014Output2654.1‖ ≤ (batchValueN02704MinusP014Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP014BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP014Output2654,
    batchN02704MinusP014Center2654, batchN02704MinusP014Error2654, embedPair2542]

theorem batchValueN02704MinusP014Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP014Output2654.1) + embedPair2542
            batchValueN02704MinusP014Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP014Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP014Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP014Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP014Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP014Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP014Output2654, pairMagnitude2542]

def batchValueN02704MinusP015Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP015Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP015Output2654.1‖ ≤ (batchValueN02704MinusP015Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP015BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP015Output2654,
    batchN02704MinusP015Center2654, batchN02704MinusP015Error2654, embedPair2542]

theorem batchValueN02704MinusP015Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP015Output2654.1) + embedPair2542
            batchValueN02704MinusP015Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP015Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP015Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP015Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP015Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP015Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP015Output2654, pairMagnitude2542]

def batchValueN02704MinusP016Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP016Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP016Output2654.1‖ ≤ (batchValueN02704MinusP016Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP016BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP016Output2654,
    batchN02704MinusP016Center2654, batchN02704MinusP016Error2654, embedPair2542]

theorem batchValueN02704MinusP016Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP016Output2654.1) + embedPair2542
            batchValueN02704MinusP016Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP016Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP016Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP016Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP016Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP016Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP016Output2654, pairMagnitude2542]

def batchValueN02704MinusP017Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP017Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP017Output2654.1‖ ≤ (batchValueN02704MinusP017Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP017BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP017Output2654,
    batchN02704MinusP017Center2654, batchN02704MinusP017Error2654, embedPair2542]

theorem batchValueN02704MinusP017Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP017Output2654.1) + embedPair2542
            batchValueN02704MinusP017Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP017Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP017Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP017Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP017Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP017Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP017Output2654, pairMagnitude2542]

def batchValueN02704MinusP018Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP018Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP018Output2654.1‖ ≤ (batchValueN02704MinusP018Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP018BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP018Output2654,
    batchN02704MinusP018Center2654, batchN02704MinusP018Error2654, embedPair2542]

theorem batchValueN02704MinusP018Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP018Output2654.1) + embedPair2542
            batchValueN02704MinusP018Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP018Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP018Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP018Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP018Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP018Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP018Output2654, pairMagnitude2542]

def batchValueN02704MinusP019Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP019Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP019Output2654.1‖ ≤ (batchValueN02704MinusP019Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP019BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP019Output2654,
    batchN02704MinusP019Center2654, batchN02704MinusP019Error2654, embedPair2542]

theorem batchValueN02704MinusP019Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP019Output2654.1) + embedPair2542
            batchValueN02704MinusP019Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP019Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP019Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP019Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP019Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP019Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP019Output2654, pairMagnitude2542]

def batchValueN02704MinusP020Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP020Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP020Output2654.1‖ ≤ (batchValueN02704MinusP020Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP020BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP020Output2654,
    batchN02704MinusP020Center2654, batchN02704MinusP020Error2654, embedPair2542]

theorem batchValueN02704MinusP020Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP020Output2654.1) + embedPair2542
            batchValueN02704MinusP020Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP020Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP020Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP020Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP020Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP020Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP020Output2654, pairMagnitude2542]

def batchValueN02704MinusP021Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP021Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP021Output2654.1‖ ≤ (batchValueN02704MinusP021Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP021BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP021Output2654,
    batchN02704MinusP021Center2654, batchN02704MinusP021Error2654, embedPair2542]

theorem batchValueN02704MinusP021Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP021Output2654.1) + embedPair2542
            batchValueN02704MinusP021Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP021Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP021Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP021Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP021Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP021Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP021Output2654, pairMagnitude2542]

def batchValueN02704MinusP022Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP022Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP022Output2654.1‖ ≤ (batchValueN02704MinusP022Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP022BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP022Output2654,
    batchN02704MinusP022Center2654, batchN02704MinusP022Error2654, embedPair2542]

theorem batchValueN02704MinusP022Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP022Output2654.1) + embedPair2542
            batchValueN02704MinusP022Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP022Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP022Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP022Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP022Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP022Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP022Output2654, pairMagnitude2542]

def batchValueN02704MinusP023Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP023Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP023Output2654.1‖ ≤ (batchValueN02704MinusP023Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP023BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP023Output2654,
    batchN02704MinusP023Center2654, batchN02704MinusP023Error2654, embedPair2542]

theorem batchValueN02704MinusP023Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP023Output2654.1) + embedPair2542
            batchValueN02704MinusP023Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP023Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP023Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP023Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP023Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP023Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP023Output2654, pairMagnitude2542]

def batchValueN02704MinusP024Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP024Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP024Output2654.1‖ ≤ (batchValueN02704MinusP024Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP024BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP024Output2654,
    batchN02704MinusP024Center2654, batchN02704MinusP024Error2654, embedPair2542]

theorem batchValueN02704MinusP024Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP024Output2654.1) + embedPair2542
            batchValueN02704MinusP024Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP024Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP024Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP024Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP024Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP024Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP024Output2654, pairMagnitude2542]

def batchValueN02704MinusP025Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP025Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP025Output2654.1‖ ≤ (batchValueN02704MinusP025Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP025BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP025Output2654,
    batchN02704MinusP025Center2654, batchN02704MinusP025Error2654, embedPair2542]

theorem batchValueN02704MinusP025Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP025Output2654.1) + embedPair2542
            batchValueN02704MinusP025Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP025Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP025Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP025Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP025Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP025Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP025Output2654, pairMagnitude2542]

def batchValueN02704MinusP026Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP026Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP026Output2654.1‖ ≤ (batchValueN02704MinusP026Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP026BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP026Output2654,
    batchN02704MinusP026Center2654, batchN02704MinusP026Error2654, embedPair2542]

theorem batchValueN02704MinusP026Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP026Output2654.1) + embedPair2542
            batchValueN02704MinusP026Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP026Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP026Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP026Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP026Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP026Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP026Output2654, pairMagnitude2542]

def batchValueN02704MinusP027Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP027Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP027Output2654.1‖ ≤ (batchValueN02704MinusP027Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP027BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP027Output2654,
    batchN02704MinusP027Center2654, batchN02704MinusP027Error2654, embedPair2542]

theorem batchValueN02704MinusP027Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP027Output2654.1) + embedPair2542
            batchValueN02704MinusP027Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP027Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP027Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP027Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP027Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP027Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP027Output2654, pairMagnitude2542]

def batchValueN02704MinusP028Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP028Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP028Output2654.1‖ ≤ (batchValueN02704MinusP028Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP028BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP028Output2654,
    batchN02704MinusP028Center2654, batchN02704MinusP028Error2654, embedPair2542]

theorem batchValueN02704MinusP028Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP028Output2654.1) + embedPair2542
            batchValueN02704MinusP028Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP028Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP028Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP028Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP028Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP028Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP028Output2654, pairMagnitude2542]

def batchValueN02704MinusP029Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704MinusP029Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP029Output2654.1‖ ≤ (batchValueN02704MinusP029Output2654.2 : ℝ)
                := by
  have h := batchN02704MinusP029BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704MinusPosition2654, batchN02704MinusPosition2654,
      batchValueN02704MinusP029Output2654,
    batchN02704MinusP029Center2654, batchN02704MinusP029Error2654, embedPair2542]

theorem batchValueN02704MinusP029Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02704MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02704MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP029Output2654.1) + embedPair2542
            batchValueN02704MinusP029Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02704MinusPosition2654 - embedPair2542
            batchValueN02704MinusP029Output2654.1‖ + ‖embedPair2542
            batchValueN02704MinusP029Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704MinusP029Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704MinusP029Output2654.1 : ℝ) :=
      add_le_add batchValueN02704MinusP029Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704MinusP029Output2654, pairMagnitude2542]

noncomputable def batchValueN02704MinusValue2654 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchValueN02704MinusP000Output2654.1
  | 1 => embedPair2542 batchValueN02704MinusP001Output2654.1
  | 2 => embedPair2542 batchValueN02704MinusP002Output2654.1
  | 3 => embedPair2542 batchValueN02704MinusP003Output2654.1
  | 4 => embedPair2542 batchValueN02704MinusP004Output2654.1
  | 5 => embedPair2542 batchValueN02704MinusP005Output2654.1
  | 6 => embedPair2542 batchValueN02704MinusP006Output2654.1
  | 7 => embedPair2542 batchValueN02704MinusP007Output2654.1
  | 8 => embedPair2542 batchValueN02704MinusP008Output2654.1
  | 9 => embedPair2542 batchValueN02704MinusP009Output2654.1
  | 10 => embedPair2542 batchValueN02704MinusP010Output2654.1
  | 11 => embedPair2542 batchValueN02704MinusP011Output2654.1
  | 12 => embedPair2542 batchValueN02704MinusP012Output2654.1
  | 13 => embedPair2542 batchValueN02704MinusP013Output2654.1
  | 14 => embedPair2542 batchValueN02704MinusP014Output2654.1
  | 15 => embedPair2542 batchValueN02704MinusP015Output2654.1
  | 16 => embedPair2542 batchValueN02704MinusP016Output2654.1
  | 17 => embedPair2542 batchValueN02704MinusP017Output2654.1
  | 18 => embedPair2542 batchValueN02704MinusP018Output2654.1
  | 19 => embedPair2542 batchValueN02704MinusP019Output2654.1
  | 20 => embedPair2542 batchValueN02704MinusP020Output2654.1
  | 21 => embedPair2542 batchValueN02704MinusP021Output2654.1
  | 22 => embedPair2542 batchValueN02704MinusP022Output2654.1
  | 23 => embedPair2542 batchValueN02704MinusP023Output2654.1
  | 24 => embedPair2542 batchValueN02704MinusP024Output2654.1
  | 25 => embedPair2542 batchValueN02704MinusP025Output2654.1
  | 26 => embedPair2542 batchValueN02704MinusP026Output2654.1
  | 27 => embedPair2542 batchValueN02704MinusP027Output2654.1
  | 28 => embedPair2542 batchValueN02704MinusP028Output2654.1
  | 29 => embedPair2542 batchValueN02704MinusP029Output2654.1
  | _ => 0

noncomputable def batchValueN02704MinusError2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (batchValueN02704MinusP000Output2654.2 : ℝ)
  | 1 => (batchValueN02704MinusP001Output2654.2 : ℝ)
  | 2 => (batchValueN02704MinusP002Output2654.2 : ℝ)
  | 3 => (batchValueN02704MinusP003Output2654.2 : ℝ)
  | 4 => (batchValueN02704MinusP004Output2654.2 : ℝ)
  | 5 => (batchValueN02704MinusP005Output2654.2 : ℝ)
  | 6 => (batchValueN02704MinusP006Output2654.2 : ℝ)
  | 7 => (batchValueN02704MinusP007Output2654.2 : ℝ)
  | 8 => (batchValueN02704MinusP008Output2654.2 : ℝ)
  | 9 => (batchValueN02704MinusP009Output2654.2 : ℝ)
  | 10 => (batchValueN02704MinusP010Output2654.2 : ℝ)
  | 11 => (batchValueN02704MinusP011Output2654.2 : ℝ)
  | 12 => (batchValueN02704MinusP012Output2654.2 : ℝ)
  | 13 => (batchValueN02704MinusP013Output2654.2 : ℝ)
  | 14 => (batchValueN02704MinusP014Output2654.2 : ℝ)
  | 15 => (batchValueN02704MinusP015Output2654.2 : ℝ)
  | 16 => (batchValueN02704MinusP016Output2654.2 : ℝ)
  | 17 => (batchValueN02704MinusP017Output2654.2 : ℝ)
  | 18 => (batchValueN02704MinusP018Output2654.2 : ℝ)
  | 19 => (batchValueN02704MinusP019Output2654.2 : ℝ)
  | 20 => (batchValueN02704MinusP020Output2654.2 : ℝ)
  | 21 => (batchValueN02704MinusP021Output2654.2 : ℝ)
  | 22 => (batchValueN02704MinusP022Output2654.2 : ℝ)
  | 23 => (batchValueN02704MinusP023Output2654.2 : ℝ)
  | 24 => (batchValueN02704MinusP024Output2654.2 : ℝ)
  | 25 => (batchValueN02704MinusP025Output2654.2 : ℝ)
  | 26 => (batchValueN02704MinusP026Output2654.2 : ℝ)
  | 27 => (batchValueN02704MinusP027Output2654.2 : ℝ)
  | 28 => (batchValueN02704MinusP028Output2654.2 : ℝ)
  | 29 => (batchValueN02704MinusP029Output2654.2 : ℝ)
  | _ => 0

theorem batchValueN02704MinusExp_error2654 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02704MinusPosition2654 -
            batchValueN02704MinusValue2654 i‖
            ≤ batchValueN02704MinusError2654 i := by
  fin_cases i
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP000Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP001Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP002Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP003Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP004Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP005Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP006Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP007Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP008Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP009Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP010Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP011Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP012Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP013Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP014Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP015Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP016Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP017Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP018Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP019Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP020Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP021Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP022Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP023Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP024Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP025Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP026Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP027Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP028Error2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP029Error2654

theorem batchValueN02704MinusUnit_norm2654 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02704MinusPosition2654‖ ≤ 1 := by
  fin_cases i
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP000Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP001Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP002Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP003Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP004Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP005Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP006Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP007Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP008Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP009Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP010Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP011Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP012Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP013Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP014Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP015Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP016Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP017Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP018Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP019Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP020Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP021Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP022Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP023Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP024Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP025Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP026Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP027Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP028Norm2654
  · simpa only [batchValueN02704MinusValue2654, batchValueN02704MinusError2654] using
      batchValueN02704MinusP029Norm2654

noncomputable def batchValueN02704MinusSumValue2654 : ℂ := ⟨(((((76460463405462118827 * 10^40
        + 546566348583922369388287982169974515126) * 10^40
        + 2160499148176173918690718202809746576619) * 10^40
        + 5478196582750946309612996866416023169727) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816)),
    (((((166230417923165420 * 10^40
        + 959465254070762146523314047733020892728) * 10^40
        + 2224157612092432481583128102439288751733) * 10^40
        + 6873716741533556139741520746292778381263) : ℝ) /
        (((195109284394749514461349 * 10^40
        + 8268620728941092873839165606969286973099) * 10^40
        + 7658573367623535125751913144146824819748) * 10^40
        + 9183195087913930965498479955517831643136))⟩

noncomputable def batchValueN02704MinusUpper2654 : ℝ := ((17521 : ℝ) /
        10000000000)

theorem batchValueN02704MinusSum_eq2654 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02704MinusValue2654 i) =
      batchValueN02704MinusSumValue2654 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN02704MinusValue2654,
      batchValueN02704MinusSumValue2654, embedPair2542, batchValueN02704MinusP000Output2654,
      batchValueN02704MinusP001Output2654,
      batchValueN02704MinusP002Output2654,
      batchValueN02704MinusP003Output2654,
      batchValueN02704MinusP004Output2654,
      batchValueN02704MinusP005Output2654,
      batchValueN02704MinusP006Output2654,
      batchValueN02704MinusP007Output2654,
      batchValueN02704MinusP008Output2654,
      batchValueN02704MinusP009Output2654,
      batchValueN02704MinusP010Output2654,
      batchValueN02704MinusP011Output2654,
      batchValueN02704MinusP012Output2654,
      batchValueN02704MinusP013Output2654,
      batchValueN02704MinusP014Output2654,
      batchValueN02704MinusP015Output2654,
      batchValueN02704MinusP016Output2654,
      batchValueN02704MinusP017Output2654,
      batchValueN02704MinusP018Output2654,
      batchValueN02704MinusP019Output2654,
      batchValueN02704MinusP020Output2654,
      batchValueN02704MinusP021Output2654,
      batchValueN02704MinusP022Output2654,
      batchValueN02704MinusP023Output2654,
      batchValueN02704MinusP024Output2654,
      batchValueN02704MinusP025Output2654,
      batchValueN02704MinusP026Output2654,
      batchValueN02704MinusP027Output2654,
      batchValueN02704MinusP028Output2654,
      batchValueN02704MinusP029Output2654, Complex.mul_re, Complex.mul_im]

theorem batchValueN02704MinusSum_norm2654 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02704MinusValue2654 i‖ ≤
      ((219 : ℝ) /
        125000000) := by
  rw [batchValueN02704MinusSum_eq2654]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchValueN02704MinusSumValue2654]

theorem batchValueN02704MinusEvaluation_charge2654 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchValueN02704MinusError2654 i) ≤ (1 : ℝ)/10^12 :=
          by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN02704MinusError2654,
      batchValueN02704MinusP000Output2654,
      batchValueN02704MinusP001Output2654,
      batchValueN02704MinusP002Output2654,
      batchValueN02704MinusP003Output2654,
      batchValueN02704MinusP004Output2654,
      batchValueN02704MinusP005Output2654,
      batchValueN02704MinusP006Output2654,
      batchValueN02704MinusP007Output2654,
      batchValueN02704MinusP008Output2654,
      batchValueN02704MinusP009Output2654,
      batchValueN02704MinusP010Output2654,
      batchValueN02704MinusP011Output2654,
      batchValueN02704MinusP012Output2654,
      batchValueN02704MinusP013Output2654,
      batchValueN02704MinusP014Output2654,
      batchValueN02704MinusP015Output2654,
      batchValueN02704MinusP016Output2654,
      batchValueN02704MinusP017Output2654,
      batchValueN02704MinusP018Output2654,
      batchValueN02704MinusP019Output2654,
      batchValueN02704MinusP020Output2654,
      batchValueN02704MinusP021Output2654,
      batchValueN02704MinusP022Output2654,
      batchValueN02704MinusP023Output2654,
      batchValueN02704MinusP024Output2654,
      batchValueN02704MinusP025Output2654,
      batchValueN02704MinusP026Output2654,
      batchValueN02704MinusP027Output2654,
      batchValueN02704MinusP028Output2654,
      batchValueN02704MinusP029Output2654]

theorem batchValueN02704MinusSigned_le2654 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchValueN02704MinusPosition2654 ≤ batchValueN02704MinusUpper2654 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02704MinusPosition2654‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02704MinusValue2654 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchValueN02704MinusError2654 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (batchValueN02704MinusExp_error2654 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02704MinusPosition2654‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchValueN02704MinusUnit_norm2654 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02704MinusPosition2654‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchValueN02704MinusUpper2654
  linarith [batchValueN02704MinusSum_norm2654, batchValueN02704MinusEvaluation_charge2654]

theorem batchValueN02704MinusPhysical_le2654 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 batchValueN02704MinusPosition2654‖ ≤
      batchValueN02704MinusUpper2654 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchValueN02704MinusPosition2654
  simpa only [iteratedDeriv_zero] using h.trans batchValueN02704MinusSigned_le2654

theorem batchValueN02704MinusGrid2654 :
    -stripRadius2303 + (2704 : ℝ)*(2*stripRadius2303/10240) = batchValueN02704MinusPosition2654 :=
        by
  norm_num [stripRadius2303, batchValueN02704MinusPosition2654]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchValueN02704MinusSigned_le2654
#print axioms ConnesWeilRH.Dev.batchValueN02704MinusPhysical_le2654
