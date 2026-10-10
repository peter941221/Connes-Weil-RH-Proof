import ConnesWeilRH.Dev.C1RouteABatchN02704Plus2654
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchValueN02704PlusPosition2654 : ℝ := (((-9895936151) : ℝ) /
        3200000000)

def batchValueN02704PlusP000Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem batchValueN02704PlusP000Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP000Output2654.1‖ ≤ (batchValueN02704PlusP000Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP000BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP000Output2654,
    batchN02704PlusP000Center2654, batchN02704PlusP000Error2654, embedPair2542]

theorem batchValueN02704PlusP000Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP000Output2654.1) + embedPair2542
            batchValueN02704PlusP000Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP000Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP000Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP000Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP000Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP000Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP000Output2654, pairMagnitude2542]

def batchValueN02704PlusP001Output2654 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP001Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP001Output2654.1‖ ≤ (batchValueN02704PlusP001Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP001BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP001Output2654,
    batchN02704PlusP001Center2654, batchN02704PlusP001Error2654, embedPair2542]

theorem batchValueN02704PlusP001Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP001Output2654.1) + embedPair2542
            batchValueN02704PlusP001Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP001Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP001Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP001Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP001Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP001Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP001Output2654, pairMagnitude2542]

def batchValueN02704PlusP002Output2654 : RatState2542 :=
  (((((-150665789589046507317) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-646605045251160912061) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((2703320551278323549 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP002Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP002Output2654.1‖ ≤ (batchValueN02704PlusP002Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP002BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP002Output2654,
    batchN02704PlusP002Center2654, batchN02704PlusP002Error2654, embedPair2542]

theorem batchValueN02704PlusP002Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP002Output2654.1) + embedPair2542
            batchValueN02704PlusP002Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP002Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP002Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP002Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP002Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP002Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP002Output2654, pairMagnitude2542]

def batchValueN02704PlusP003Output2654 : RatState2542 :=
  (((((-2337165949435292114676855823) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-10030301494560025509101554821) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((39308232611829201955562319 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP003Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP003Output2654.1‖ ≤ (batchValueN02704PlusP003Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP003BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP003Output2654,
    batchN02704PlusP003Center2654, batchN02704PlusP003Error2654, embedPair2542]

theorem batchValueN02704PlusP003Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP003Output2654.1) + embedPair2542
            batchValueN02704PlusP003Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP003Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP003Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP003Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP003Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP003Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP003Output2654, pairMagnitude2542]

def batchValueN02704PlusP004Output2654 : RatState2542 :=
  (((((-2280774527693167736821574979679) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((2447072292770089851661591621051 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((18721683894319600454709178461 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP004Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP004Output2654.1‖ ≤ (batchValueN02704PlusP004Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP004BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP004Output2654,
    batchN02704PlusP004Center2654, batchN02704PlusP004Error2654, embedPair2542]

theorem batchValueN02704PlusP004Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP004Output2654.1) + embedPair2542
            batchValueN02704PlusP004Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP004Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP004Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP004Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP004Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP004Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP004Output2654, pairMagnitude2542]

def batchValueN02704PlusP005Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem batchValueN02704PlusP005Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP005Output2654.1‖ ≤ (batchValueN02704PlusP005Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP005BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP005Output2654,
    batchN02704PlusP005Center2654, batchN02704PlusP005Error2654, embedPair2542]

theorem batchValueN02704PlusP005Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP005Output2654.1) + embedPair2542
            batchValueN02704PlusP005Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP005Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP005Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP005Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP005Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP005Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP005Output2654, pairMagnitude2542]

def batchValueN02704PlusP006Output2654 : RatState2542 :=
  ((((638567541572489 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((2524797428367 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP006Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP006Output2654.1‖ ≤ (batchValueN02704PlusP006Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP006BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP006Output2654,
    batchN02704PlusP006Center2654, batchN02704PlusP006Error2654, embedPair2542]

theorem batchValueN02704PlusP006Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP006Output2654.1) + embedPair2542
            batchValueN02704PlusP006Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP006Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP006Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP006Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP006Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP006Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP006Output2654, pairMagnitude2542]

def batchValueN02704PlusP007Output2654 : RatState2542 :=
  ((((11065998679404049300331925531 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((803023130034719983008463 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN02704PlusP007Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP007Output2654.1‖ ≤ (batchValueN02704PlusP007Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP007BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP007Output2654,
    batchN02704PlusP007Center2654, batchN02704PlusP007Error2654, embedPair2542]

theorem batchValueN02704PlusP007Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP007Output2654.1) + embedPair2542
            batchValueN02704PlusP007Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP007Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP007Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP007Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP007Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP007Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP007Output2654, pairMagnitude2542]

def batchValueN02704PlusP008Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP008Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP008Output2654.1‖ ≤ (batchValueN02704PlusP008Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP008BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP008Output2654,
    batchN02704PlusP008Center2654, batchN02704PlusP008Error2654, embedPair2542]

theorem batchValueN02704PlusP008Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP008Output2654.1) + embedPair2542
            batchValueN02704PlusP008Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP008Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP008Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP008Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP008Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP008Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP008Output2654, pairMagnitude2542]

def batchValueN02704PlusP009Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP009Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP009Output2654.1‖ ≤ (batchValueN02704PlusP009Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP009BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP009Output2654,
    batchN02704PlusP009Center2654, batchN02704PlusP009Error2654, embedPair2542]

theorem batchValueN02704PlusP009Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP009Output2654.1) + embedPair2542
            batchValueN02704PlusP009Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP009Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP009Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP009Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP009Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP009Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP009Output2654, pairMagnitude2542]

def batchValueN02704PlusP010Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP010Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP010Output2654.1‖ ≤ (batchValueN02704PlusP010Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP010BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP010Output2654,
    batchN02704PlusP010Center2654, batchN02704PlusP010Error2654, embedPair2542]

theorem batchValueN02704PlusP010Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP010Output2654.1) + embedPair2542
            batchValueN02704PlusP010Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP010Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP010Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP010Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP010Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP010Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP010Output2654, pairMagnitude2542]

def batchValueN02704PlusP011Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP011Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP011Output2654.1‖ ≤ (batchValueN02704PlusP011Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP011BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP011Output2654,
    batchN02704PlusP011Center2654, batchN02704PlusP011Error2654, embedPair2542]

theorem batchValueN02704PlusP011Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP011Output2654.1) + embedPair2542
            batchValueN02704PlusP011Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP011Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP011Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP011Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP011Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP011Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP011Output2654, pairMagnitude2542]

def batchValueN02704PlusP012Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP012Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP012Output2654.1‖ ≤ (batchValueN02704PlusP012Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP012BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP012Output2654,
    batchN02704PlusP012Center2654, batchN02704PlusP012Error2654, embedPair2542]

theorem batchValueN02704PlusP012Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP012Output2654.1) + embedPair2542
            batchValueN02704PlusP012Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP012Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP012Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP012Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP012Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP012Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP012Output2654, pairMagnitude2542]

def batchValueN02704PlusP013Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP013Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP013Output2654.1‖ ≤ (batchValueN02704PlusP013Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP013BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP013Output2654,
    batchN02704PlusP013Center2654, batchN02704PlusP013Error2654, embedPair2542]

theorem batchValueN02704PlusP013Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP013Output2654.1) + embedPair2542
            batchValueN02704PlusP013Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP013Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP013Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP013Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP013Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP013Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP013Output2654, pairMagnitude2542]

def batchValueN02704PlusP014Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP014Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP014Output2654.1‖ ≤ (batchValueN02704PlusP014Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP014BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP014Output2654,
    batchN02704PlusP014Center2654, batchN02704PlusP014Error2654, embedPair2542]

theorem batchValueN02704PlusP014Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP014Output2654.1) + embedPair2542
            batchValueN02704PlusP014Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP014Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP014Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP014Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP014Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP014Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP014Output2654, pairMagnitude2542]

def batchValueN02704PlusP015Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP015Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP015Output2654.1‖ ≤ (batchValueN02704PlusP015Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP015BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP015Output2654,
    batchN02704PlusP015Center2654, batchN02704PlusP015Error2654, embedPair2542]

theorem batchValueN02704PlusP015Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP015Output2654.1) + embedPair2542
            batchValueN02704PlusP015Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP015Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP015Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP015Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP015Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP015Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP015Output2654, pairMagnitude2542]

def batchValueN02704PlusP016Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP016Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP016Output2654.1‖ ≤ (batchValueN02704PlusP016Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP016BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP016Output2654,
    batchN02704PlusP016Center2654, batchN02704PlusP016Error2654, embedPair2542]

theorem batchValueN02704PlusP016Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP016Output2654.1) + embedPair2542
            batchValueN02704PlusP016Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP016Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP016Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP016Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP016Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP016Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP016Output2654, pairMagnitude2542]

def batchValueN02704PlusP017Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP017Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP017Output2654.1‖ ≤ (batchValueN02704PlusP017Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP017BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP017Output2654,
    batchN02704PlusP017Center2654, batchN02704PlusP017Error2654, embedPair2542]

theorem batchValueN02704PlusP017Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP017Output2654.1) + embedPair2542
            batchValueN02704PlusP017Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP017Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP017Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP017Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP017Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP017Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP017Output2654, pairMagnitude2542]

def batchValueN02704PlusP018Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP018Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP018Output2654.1‖ ≤ (batchValueN02704PlusP018Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP018BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP018Output2654,
    batchN02704PlusP018Center2654, batchN02704PlusP018Error2654, embedPair2542]

theorem batchValueN02704PlusP018Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP018Output2654.1) + embedPair2542
            batchValueN02704PlusP018Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP018Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP018Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP018Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP018Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP018Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP018Output2654, pairMagnitude2542]

def batchValueN02704PlusP019Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP019Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP019Output2654.1‖ ≤ (batchValueN02704PlusP019Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP019BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP019Output2654,
    batchN02704PlusP019Center2654, batchN02704PlusP019Error2654, embedPair2542]

theorem batchValueN02704PlusP019Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP019Output2654.1) + embedPair2542
            batchValueN02704PlusP019Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP019Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP019Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP019Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP019Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP019Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP019Output2654, pairMagnitude2542]

def batchValueN02704PlusP020Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP020Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP020Output2654.1‖ ≤ (batchValueN02704PlusP020Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP020BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP020Output2654,
    batchN02704PlusP020Center2654, batchN02704PlusP020Error2654, embedPair2542]

theorem batchValueN02704PlusP020Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP020Output2654.1) + embedPair2542
            batchValueN02704PlusP020Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP020Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP020Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP020Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP020Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP020Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP020Output2654, pairMagnitude2542]

def batchValueN02704PlusP021Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP021Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP021Output2654.1‖ ≤ (batchValueN02704PlusP021Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP021BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP021Output2654,
    batchN02704PlusP021Center2654, batchN02704PlusP021Error2654, embedPair2542]

theorem batchValueN02704PlusP021Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP021Output2654.1) + embedPair2542
            batchValueN02704PlusP021Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP021Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP021Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP021Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP021Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP021Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP021Output2654, pairMagnitude2542]

def batchValueN02704PlusP022Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP022Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP022Output2654.1‖ ≤ (batchValueN02704PlusP022Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP022BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP022Output2654,
    batchN02704PlusP022Center2654, batchN02704PlusP022Error2654, embedPair2542]

theorem batchValueN02704PlusP022Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP022Output2654.1) + embedPair2542
            batchValueN02704PlusP022Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP022Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP022Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP022Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP022Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP022Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP022Output2654, pairMagnitude2542]

def batchValueN02704PlusP023Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP023Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP023Output2654.1‖ ≤ (batchValueN02704PlusP023Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP023BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP023Output2654,
    batchN02704PlusP023Center2654, batchN02704PlusP023Error2654, embedPair2542]

theorem batchValueN02704PlusP023Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP023Output2654.1) + embedPair2542
            batchValueN02704PlusP023Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP023Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP023Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP023Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP023Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP023Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP023Output2654, pairMagnitude2542]

def batchValueN02704PlusP024Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP024Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP024Output2654.1‖ ≤ (batchValueN02704PlusP024Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP024BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP024Output2654,
    batchN02704PlusP024Center2654, batchN02704PlusP024Error2654, embedPair2542]

theorem batchValueN02704PlusP024Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP024Output2654.1) + embedPair2542
            batchValueN02704PlusP024Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP024Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP024Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP024Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP024Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP024Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP024Output2654, pairMagnitude2542]

def batchValueN02704PlusP025Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP025Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP025Output2654.1‖ ≤ (batchValueN02704PlusP025Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP025BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP025Output2654,
    batchN02704PlusP025Center2654, batchN02704PlusP025Error2654, embedPair2542]

theorem batchValueN02704PlusP025Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP025Output2654.1) + embedPair2542
            batchValueN02704PlusP025Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP025Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP025Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP025Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP025Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP025Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP025Output2654, pairMagnitude2542]

def batchValueN02704PlusP026Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP026Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP026Output2654.1‖ ≤ (batchValueN02704PlusP026Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP026BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP026Output2654,
    batchN02704PlusP026Center2654, batchN02704PlusP026Error2654, embedPair2542]

theorem batchValueN02704PlusP026Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP026Output2654.1) + embedPair2542
            batchValueN02704PlusP026Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP026Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP026Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP026Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP026Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP026Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP026Output2654, pairMagnitude2542]

def batchValueN02704PlusP027Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP027Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP027Output2654.1‖ ≤ (batchValueN02704PlusP027Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP027BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP027Output2654,
    batchN02704PlusP027Center2654, batchN02704PlusP027Error2654, embedPair2542]

theorem batchValueN02704PlusP027Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP027Output2654.1) + embedPair2542
            batchValueN02704PlusP027Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP027Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP027Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP027Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP027Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP027Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP027Output2654, pairMagnitude2542]

def batchValueN02704PlusP028Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP028Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP028Output2654.1‖ ≤ (batchValueN02704PlusP028Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP028BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP028Output2654,
    batchN02704PlusP028Center2654, batchN02704PlusP028Error2654, embedPair2542]

theorem batchValueN02704PlusP028Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP028Output2654.1) + embedPair2542
            batchValueN02704PlusP028Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP028Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP028Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP028Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP028Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP028Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP028Output2654, pairMagnitude2542]

def batchValueN02704PlusP029Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02704PlusP029Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP029Output2654.1‖ ≤ (batchValueN02704PlusP029Output2654.2 : ℝ) :=
                by
  have h := batchN02704PlusP029BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02704PlusPosition2654, batchN02704PlusPosition2654,
      batchValueN02704PlusP029Output2654,
    batchN02704PlusP029Center2654, batchN02704PlusP029Error2654, embedPair2542]

theorem batchValueN02704PlusP029Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02704PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02704PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP029Output2654.1) + embedPair2542
            batchValueN02704PlusP029Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02704PlusPosition2654 - embedPair2542
            batchValueN02704PlusP029Output2654.1‖ + ‖embedPair2542
            batchValueN02704PlusP029Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02704PlusP029Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02704PlusP029Output2654.1 : ℝ) :=
      add_le_add batchValueN02704PlusP029Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02704PlusP029Output2654, pairMagnitude2542]

noncomputable def batchValueN02704PlusValue2654 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchValueN02704PlusP000Output2654.1
  | 1 => embedPair2542 batchValueN02704PlusP001Output2654.1
  | 2 => embedPair2542 batchValueN02704PlusP002Output2654.1
  | 3 => embedPair2542 batchValueN02704PlusP003Output2654.1
  | 4 => embedPair2542 batchValueN02704PlusP004Output2654.1
  | 5 => embedPair2542 batchValueN02704PlusP005Output2654.1
  | 6 => embedPair2542 batchValueN02704PlusP006Output2654.1
  | 7 => embedPair2542 batchValueN02704PlusP007Output2654.1
  | 8 => embedPair2542 batchValueN02704PlusP008Output2654.1
  | 9 => embedPair2542 batchValueN02704PlusP009Output2654.1
  | 10 => embedPair2542 batchValueN02704PlusP010Output2654.1
  | 11 => embedPair2542 batchValueN02704PlusP011Output2654.1
  | 12 => embedPair2542 batchValueN02704PlusP012Output2654.1
  | 13 => embedPair2542 batchValueN02704PlusP013Output2654.1
  | 14 => embedPair2542 batchValueN02704PlusP014Output2654.1
  | 15 => embedPair2542 batchValueN02704PlusP015Output2654.1
  | 16 => embedPair2542 batchValueN02704PlusP016Output2654.1
  | 17 => embedPair2542 batchValueN02704PlusP017Output2654.1
  | 18 => embedPair2542 batchValueN02704PlusP018Output2654.1
  | 19 => embedPair2542 batchValueN02704PlusP019Output2654.1
  | 20 => embedPair2542 batchValueN02704PlusP020Output2654.1
  | 21 => embedPair2542 batchValueN02704PlusP021Output2654.1
  | 22 => embedPair2542 batchValueN02704PlusP022Output2654.1
  | 23 => embedPair2542 batchValueN02704PlusP023Output2654.1
  | 24 => embedPair2542 batchValueN02704PlusP024Output2654.1
  | 25 => embedPair2542 batchValueN02704PlusP025Output2654.1
  | 26 => embedPair2542 batchValueN02704PlusP026Output2654.1
  | 27 => embedPair2542 batchValueN02704PlusP027Output2654.1
  | 28 => embedPair2542 batchValueN02704PlusP028Output2654.1
  | 29 => embedPair2542 batchValueN02704PlusP029Output2654.1
  | _ => 0

noncomputable def batchValueN02704PlusError2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (batchValueN02704PlusP000Output2654.2 : ℝ)
  | 1 => (batchValueN02704PlusP001Output2654.2 : ℝ)
  | 2 => (batchValueN02704PlusP002Output2654.2 : ℝ)
  | 3 => (batchValueN02704PlusP003Output2654.2 : ℝ)
  | 4 => (batchValueN02704PlusP004Output2654.2 : ℝ)
  | 5 => (batchValueN02704PlusP005Output2654.2 : ℝ)
  | 6 => (batchValueN02704PlusP006Output2654.2 : ℝ)
  | 7 => (batchValueN02704PlusP007Output2654.2 : ℝ)
  | 8 => (batchValueN02704PlusP008Output2654.2 : ℝ)
  | 9 => (batchValueN02704PlusP009Output2654.2 : ℝ)
  | 10 => (batchValueN02704PlusP010Output2654.2 : ℝ)
  | 11 => (batchValueN02704PlusP011Output2654.2 : ℝ)
  | 12 => (batchValueN02704PlusP012Output2654.2 : ℝ)
  | 13 => (batchValueN02704PlusP013Output2654.2 : ℝ)
  | 14 => (batchValueN02704PlusP014Output2654.2 : ℝ)
  | 15 => (batchValueN02704PlusP015Output2654.2 : ℝ)
  | 16 => (batchValueN02704PlusP016Output2654.2 : ℝ)
  | 17 => (batchValueN02704PlusP017Output2654.2 : ℝ)
  | 18 => (batchValueN02704PlusP018Output2654.2 : ℝ)
  | 19 => (batchValueN02704PlusP019Output2654.2 : ℝ)
  | 20 => (batchValueN02704PlusP020Output2654.2 : ℝ)
  | 21 => (batchValueN02704PlusP021Output2654.2 : ℝ)
  | 22 => (batchValueN02704PlusP022Output2654.2 : ℝ)
  | 23 => (batchValueN02704PlusP023Output2654.2 : ℝ)
  | 24 => (batchValueN02704PlusP024Output2654.2 : ℝ)
  | 25 => (batchValueN02704PlusP025Output2654.2 : ℝ)
  | 26 => (batchValueN02704PlusP026Output2654.2 : ℝ)
  | 27 => (batchValueN02704PlusP027Output2654.2 : ℝ)
  | 28 => (batchValueN02704PlusP028Output2654.2 : ℝ)
  | 29 => (batchValueN02704PlusP029Output2654.2 : ℝ)
  | _ => 0

theorem batchValueN02704PlusExp_error2654 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02704PlusPosition2654 - batchValueN02704PlusValue2654
            i‖ ≤
            batchValueN02704PlusError2654 i := by
  fin_cases i
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP000Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP001Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP002Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP003Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP004Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP005Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP006Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP007Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP008Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP009Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP010Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP011Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP012Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP013Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP014Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP015Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP016Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP017Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP018Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP019Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP020Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP021Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP022Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP023Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP024Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP025Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP026Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP027Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP028Error2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP029Error2654

theorem batchValueN02704PlusUnit_norm2654 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02704PlusPosition2654‖ ≤ 1 := by
  fin_cases i
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP000Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP001Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP002Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP003Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP004Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP005Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP006Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP007Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP008Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP009Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP010Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP011Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP012Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP013Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP014Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP015Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP016Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP017Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP018Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP019Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP020Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP021Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP022Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP023Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP024Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP025Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP026Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP027Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP028Norm2654
  · simpa only [batchValueN02704PlusValue2654, batchValueN02704PlusError2654] using
      batchValueN02704PlusP029Norm2654

noncomputable def batchValueN02704PlusSumValue2654 : ℂ := ⟨(((((3470482876670422259 * 10^40
        + 7635175847950189062335080661012791336138) * 10^40
        + 5618348343020829257510815592617072521607) * 10^40
        + 2737539067937547830333941143274965568043) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816)),
    (((((965769412596725113 * 10^40
        + 1357008630020222714771845842014706222218) * 10^40
        + 3268183625456302219591288150797547705361) * 10^40
        + 7562084269928502951348358186391445030549) : ℝ) /
        (((24973988402527937851052777 * 10^40
        + 8383453304459887851413197692068732556770) * 10^40
        + 297391055812496096244882450793576927861) * 10^40
        + 5448971252983163583805434306282450321408))⟩

noncomputable def batchValueN02704PlusUpper2654 : ℝ := ((797 : ℝ) /
        10000000000)

theorem batchValueN02704PlusSum_eq2654 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02704PlusValue2654 i) =
      batchValueN02704PlusSumValue2654 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN02704PlusValue2654,
      batchValueN02704PlusSumValue2654, embedPair2542, batchValueN02704PlusP000Output2654,
      batchValueN02704PlusP001Output2654,
      batchValueN02704PlusP002Output2654,
      batchValueN02704PlusP003Output2654,
      batchValueN02704PlusP004Output2654,
      batchValueN02704PlusP005Output2654,
      batchValueN02704PlusP006Output2654,
      batchValueN02704PlusP007Output2654,
      batchValueN02704PlusP008Output2654,
      batchValueN02704PlusP009Output2654,
      batchValueN02704PlusP010Output2654,
      batchValueN02704PlusP011Output2654,
      batchValueN02704PlusP012Output2654,
      batchValueN02704PlusP013Output2654,
      batchValueN02704PlusP014Output2654,
      batchValueN02704PlusP015Output2654,
      batchValueN02704PlusP016Output2654,
      batchValueN02704PlusP017Output2654,
      batchValueN02704PlusP018Output2654,
      batchValueN02704PlusP019Output2654,
      batchValueN02704PlusP020Output2654,
      batchValueN02704PlusP021Output2654,
      batchValueN02704PlusP022Output2654,
      batchValueN02704PlusP023Output2654,
      batchValueN02704PlusP024Output2654,
      batchValueN02704PlusP025Output2654,
      batchValueN02704PlusP026Output2654,
      batchValueN02704PlusP027Output2654,
      batchValueN02704PlusP028Output2654,
      batchValueN02704PlusP029Output2654, Complex.mul_re, Complex.mul_im]

theorem batchValueN02704PlusSum_norm2654 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02704PlusValue2654 i‖ ≤
      ((199 : ℝ) /
        2500000000) := by
  rw [batchValueN02704PlusSum_eq2654]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchValueN02704PlusSumValue2654]

theorem batchValueN02704PlusEvaluation_charge2654 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchValueN02704PlusError2654 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN02704PlusError2654,
      batchValueN02704PlusP000Output2654,
      batchValueN02704PlusP001Output2654,
      batchValueN02704PlusP002Output2654,
      batchValueN02704PlusP003Output2654,
      batchValueN02704PlusP004Output2654,
      batchValueN02704PlusP005Output2654,
      batchValueN02704PlusP006Output2654,
      batchValueN02704PlusP007Output2654,
      batchValueN02704PlusP008Output2654,
      batchValueN02704PlusP009Output2654,
      batchValueN02704PlusP010Output2654,
      batchValueN02704PlusP011Output2654,
      batchValueN02704PlusP012Output2654,
      batchValueN02704PlusP013Output2654,
      batchValueN02704PlusP014Output2654,
      batchValueN02704PlusP015Output2654,
      batchValueN02704PlusP016Output2654,
      batchValueN02704PlusP017Output2654,
      batchValueN02704PlusP018Output2654,
      batchValueN02704PlusP019Output2654,
      batchValueN02704PlusP020Output2654,
      batchValueN02704PlusP021Output2654,
      batchValueN02704PlusP022Output2654,
      batchValueN02704PlusP023Output2654,
      batchValueN02704PlusP024Output2654,
      batchValueN02704PlusP025Output2654,
      batchValueN02704PlusP026Output2654,
      batchValueN02704PlusP027Output2654,
      batchValueN02704PlusP028Output2654,
      batchValueN02704PlusP029Output2654]

theorem batchValueN02704PlusSigned_le2654 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchValueN02704PlusPosition2654 ≤ batchValueN02704PlusUpper2654 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02704PlusPosition2654‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02704PlusValue2654 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchValueN02704PlusError2654 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (batchValueN02704PlusExp_error2654 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02704PlusPosition2654‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchValueN02704PlusUnit_norm2654 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02704PlusPosition2654‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchValueN02704PlusUpper2654
  linarith [batchValueN02704PlusSum_norm2654, batchValueN02704PlusEvaluation_charge2654]

theorem batchValueN02704PlusPhysical_le2654 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 batchValueN02704PlusPosition2654‖ ≤
      batchValueN02704PlusUpper2654 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchValueN02704PlusPosition2654
  simpa only [iteratedDeriv_zero] using h.trans batchValueN02704PlusSigned_le2654

theorem batchValueN02704PlusGrid2654 :
    -stripRadius2303 + (2704 : ℝ)*(2*stripRadius2303/10240) = batchValueN02704PlusPosition2654 :=
        by
  norm_num [stripRadius2303, batchValueN02704PlusPosition2654]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchValueN02704PlusSigned_le2654
#print axioms ConnesWeilRH.Dev.batchValueN02704PlusPhysical_le2654
