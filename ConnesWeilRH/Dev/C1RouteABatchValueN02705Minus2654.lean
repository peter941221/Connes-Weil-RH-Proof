import ConnesWeilRH.Dev.C1RouteABatchN02705Minus2654
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchValueN02705MinusPosition2654 : ℝ := (((-31653888483) : ℝ) /
        10240000000)

def batchValueN02705MinusP000Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem batchValueN02705MinusP000Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP000Output2654.1‖ ≤ (batchValueN02705MinusP000Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP000BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP000Output2654,
    batchN02705MinusP000Center2654, batchN02705MinusP000Error2654, embedPair2542]

theorem batchValueN02705MinusP000Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP000Output2654.1) + embedPair2542
            batchValueN02705MinusP000Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP000Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP000Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP000Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP000Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP000Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP000Output2654, pairMagnitude2542]

def batchValueN02705MinusP001Output2654 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP001Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP001Output2654.1‖ ≤ (batchValueN02705MinusP001Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP001BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP001Output2654,
    batchN02705MinusP001Center2654, batchN02705MinusP001Error2654, embedPair2542]

theorem batchValueN02705MinusP001Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP001Output2654.1) + embedPair2542
            batchValueN02705MinusP001Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP001Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP001Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP001Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP001Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP001Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP001Output2654, pairMagnitude2542]

def batchValueN02705MinusP002Output2654 : RatState2542 :=
  (((((-6232910466508290662095) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-7671910554999950297919) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((62258049251692668505 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP002Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP002Output2654.1‖ ≤ (batchValueN02705MinusP002Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP002BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP002Output2654,
    batchN02705MinusP002Center2654, batchN02705MinusP002Error2654, embedPair2542]

theorem batchValueN02705MinusP002Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP002Output2654.1) + embedPair2542
            batchValueN02705MinusP002Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP002Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP002Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP002Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP002Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP002Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP002Output2654, pairMagnitude2542]

def batchValueN02705MinusP003Output2654 : RatState2542 :=
  (((((-93385857423547319201975676215) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-229891941848088526221276769381) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((874492453823048358099631199 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP003Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP003Output2654.1‖ ≤ (batchValueN02705MinusP003Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP003BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP003Output2654,
    batchN02705MinusP003Center2654, batchN02705MinusP003Error2654, embedPair2542]

theorem batchValueN02705MinusP003Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP003Output2654.1) + embedPair2542
            batchValueN02705MinusP003Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP003Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP003Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP003Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP003Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP003Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP003Output2654, pairMagnitude2542]

def batchValueN02705MinusP004Output2654 : RatState2542 :=
  (((((-5644135271377406361162294963633) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((55577632561868580858707835001315 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((412739842713913026403732476439 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP004Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP004Output2654.1‖ ≤ (batchValueN02705MinusP004Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP004BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP004Output2654,
    batchN02705MinusP004Center2654, batchN02705MinusP004Error2654, embedPair2542]

theorem batchValueN02705MinusP004Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP004Output2654.1) + embedPair2542
            batchValueN02705MinusP004Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP004Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP004Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP004Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP004Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP004Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP004Output2654, pairMagnitude2542]

def batchValueN02705MinusP005Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem batchValueN02705MinusP005Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP005Output2654.1‖ ≤ (batchValueN02705MinusP005Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP005BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP005Output2654,
    batchN02705MinusP005Center2654, batchN02705MinusP005Error2654, embedPair2542]

theorem batchValueN02705MinusP005Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP005Output2654.1) + embedPair2542
            batchValueN02705MinusP005Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP005Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP005Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP005Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP005Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP005Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP005Output2654, pairMagnitude2542]

def batchValueN02705MinusP006Output2654 : RatState2542 :=
  ((((30816524370707993 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((4933337008969 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN02705MinusP006Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP006Output2654.1‖ ≤ (batchValueN02705MinusP006Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP006BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP006Output2654,
    batchN02705MinusP006Center2654, batchN02705MinusP006Error2654, embedPair2542]

theorem batchValueN02705MinusP006Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP006Output2654.1) + embedPair2542
            batchValueN02705MinusP006Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP006Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP006Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP006Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP006Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP006Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP006Output2654, pairMagnitude2542]

def batchValueN02705MinusP007Output2654 : RatState2542 :=
  ((((248135493820243347566162584705 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((17152272637126015450671225 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN02705MinusP007Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP007Output2654.1‖ ≤ (batchValueN02705MinusP007Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP007BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP007Output2654,
    batchN02705MinusP007Center2654, batchN02705MinusP007Error2654, embedPair2542]

theorem batchValueN02705MinusP007Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP007Output2654.1) + embedPair2542
            batchValueN02705MinusP007Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP007Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP007Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP007Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP007Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP007Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP007Output2654, pairMagnitude2542]

def batchValueN02705MinusP008Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP008Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP008Output2654.1‖ ≤ (batchValueN02705MinusP008Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP008BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP008Output2654,
    batchN02705MinusP008Center2654, batchN02705MinusP008Error2654, embedPair2542]

theorem batchValueN02705MinusP008Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP008Output2654.1) + embedPair2542
            batchValueN02705MinusP008Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP008Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP008Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP008Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP008Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP008Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP008Output2654, pairMagnitude2542]

def batchValueN02705MinusP009Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP009Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP009Output2654.1‖ ≤ (batchValueN02705MinusP009Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP009BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP009Output2654,
    batchN02705MinusP009Center2654, batchN02705MinusP009Error2654, embedPair2542]

theorem batchValueN02705MinusP009Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP009Output2654.1) + embedPair2542
            batchValueN02705MinusP009Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP009Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP009Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP009Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP009Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP009Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP009Output2654, pairMagnitude2542]

def batchValueN02705MinusP010Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP010Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP010Output2654.1‖ ≤ (batchValueN02705MinusP010Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP010BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP010Output2654,
    batchN02705MinusP010Center2654, batchN02705MinusP010Error2654, embedPair2542]

theorem batchValueN02705MinusP010Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP010Output2654.1) + embedPair2542
            batchValueN02705MinusP010Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP010Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP010Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP010Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP010Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP010Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP010Output2654, pairMagnitude2542]

def batchValueN02705MinusP011Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP011Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP011Output2654.1‖ ≤ (batchValueN02705MinusP011Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP011BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP011Output2654,
    batchN02705MinusP011Center2654, batchN02705MinusP011Error2654, embedPair2542]

theorem batchValueN02705MinusP011Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP011Output2654.1) + embedPair2542
            batchValueN02705MinusP011Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP011Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP011Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP011Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP011Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP011Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP011Output2654, pairMagnitude2542]

def batchValueN02705MinusP012Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP012Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP012Output2654.1‖ ≤ (batchValueN02705MinusP012Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP012BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP012Output2654,
    batchN02705MinusP012Center2654, batchN02705MinusP012Error2654, embedPair2542]

theorem batchValueN02705MinusP012Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP012Output2654.1) + embedPair2542
            batchValueN02705MinusP012Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP012Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP012Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP012Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP012Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP012Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP012Output2654, pairMagnitude2542]

def batchValueN02705MinusP013Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP013Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP013Output2654.1‖ ≤ (batchValueN02705MinusP013Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP013BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP013Output2654,
    batchN02705MinusP013Center2654, batchN02705MinusP013Error2654, embedPair2542]

theorem batchValueN02705MinusP013Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP013Output2654.1) + embedPair2542
            batchValueN02705MinusP013Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP013Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP013Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP013Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP013Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP013Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP013Output2654, pairMagnitude2542]

def batchValueN02705MinusP014Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP014Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP014Output2654.1‖ ≤ (batchValueN02705MinusP014Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP014BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP014Output2654,
    batchN02705MinusP014Center2654, batchN02705MinusP014Error2654, embedPair2542]

theorem batchValueN02705MinusP014Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP014Output2654.1) + embedPair2542
            batchValueN02705MinusP014Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP014Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP014Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP014Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP014Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP014Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP014Output2654, pairMagnitude2542]

def batchValueN02705MinusP015Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP015Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP015Output2654.1‖ ≤ (batchValueN02705MinusP015Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP015BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP015Output2654,
    batchN02705MinusP015Center2654, batchN02705MinusP015Error2654, embedPair2542]

theorem batchValueN02705MinusP015Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP015Output2654.1) + embedPair2542
            batchValueN02705MinusP015Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP015Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP015Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP015Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP015Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP015Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP015Output2654, pairMagnitude2542]

def batchValueN02705MinusP016Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP016Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP016Output2654.1‖ ≤ (batchValueN02705MinusP016Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP016BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP016Output2654,
    batchN02705MinusP016Center2654, batchN02705MinusP016Error2654, embedPair2542]

theorem batchValueN02705MinusP016Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP016Output2654.1) + embedPair2542
            batchValueN02705MinusP016Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP016Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP016Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP016Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP016Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP016Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP016Output2654, pairMagnitude2542]

def batchValueN02705MinusP017Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP017Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP017Output2654.1‖ ≤ (batchValueN02705MinusP017Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP017BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP017Output2654,
    batchN02705MinusP017Center2654, batchN02705MinusP017Error2654, embedPair2542]

theorem batchValueN02705MinusP017Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP017Output2654.1) + embedPair2542
            batchValueN02705MinusP017Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP017Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP017Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP017Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP017Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP017Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP017Output2654, pairMagnitude2542]

def batchValueN02705MinusP018Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP018Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP018Output2654.1‖ ≤ (batchValueN02705MinusP018Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP018BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP018Output2654,
    batchN02705MinusP018Center2654, batchN02705MinusP018Error2654, embedPair2542]

theorem batchValueN02705MinusP018Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP018Output2654.1) + embedPair2542
            batchValueN02705MinusP018Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP018Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP018Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP018Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP018Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP018Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP018Output2654, pairMagnitude2542]

def batchValueN02705MinusP019Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP019Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP019Output2654.1‖ ≤ (batchValueN02705MinusP019Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP019BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP019Output2654,
    batchN02705MinusP019Center2654, batchN02705MinusP019Error2654, embedPair2542]

theorem batchValueN02705MinusP019Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP019Output2654.1) + embedPair2542
            batchValueN02705MinusP019Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP019Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP019Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP019Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP019Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP019Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP019Output2654, pairMagnitude2542]

def batchValueN02705MinusP020Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP020Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP020Output2654.1‖ ≤ (batchValueN02705MinusP020Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP020BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP020Output2654,
    batchN02705MinusP020Center2654, batchN02705MinusP020Error2654, embedPair2542]

theorem batchValueN02705MinusP020Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP020Output2654.1) + embedPair2542
            batchValueN02705MinusP020Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP020Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP020Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP020Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP020Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP020Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP020Output2654, pairMagnitude2542]

def batchValueN02705MinusP021Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP021Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP021Output2654.1‖ ≤ (batchValueN02705MinusP021Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP021BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP021Output2654,
    batchN02705MinusP021Center2654, batchN02705MinusP021Error2654, embedPair2542]

theorem batchValueN02705MinusP021Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP021Output2654.1) + embedPair2542
            batchValueN02705MinusP021Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP021Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP021Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP021Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP021Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP021Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP021Output2654, pairMagnitude2542]

def batchValueN02705MinusP022Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP022Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP022Output2654.1‖ ≤ (batchValueN02705MinusP022Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP022BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP022Output2654,
    batchN02705MinusP022Center2654, batchN02705MinusP022Error2654, embedPair2542]

theorem batchValueN02705MinusP022Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP022Output2654.1) + embedPair2542
            batchValueN02705MinusP022Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP022Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP022Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP022Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP022Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP022Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP022Output2654, pairMagnitude2542]

def batchValueN02705MinusP023Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP023Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP023Output2654.1‖ ≤ (batchValueN02705MinusP023Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP023BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP023Output2654,
    batchN02705MinusP023Center2654, batchN02705MinusP023Error2654, embedPair2542]

theorem batchValueN02705MinusP023Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP023Output2654.1) + embedPair2542
            batchValueN02705MinusP023Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP023Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP023Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP023Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP023Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP023Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP023Output2654, pairMagnitude2542]

def batchValueN02705MinusP024Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP024Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP024Output2654.1‖ ≤ (batchValueN02705MinusP024Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP024BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP024Output2654,
    batchN02705MinusP024Center2654, batchN02705MinusP024Error2654, embedPair2542]

theorem batchValueN02705MinusP024Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP024Output2654.1) + embedPair2542
            batchValueN02705MinusP024Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP024Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP024Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP024Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP024Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP024Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP024Output2654, pairMagnitude2542]

def batchValueN02705MinusP025Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP025Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP025Output2654.1‖ ≤ (batchValueN02705MinusP025Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP025BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP025Output2654,
    batchN02705MinusP025Center2654, batchN02705MinusP025Error2654, embedPair2542]

theorem batchValueN02705MinusP025Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP025Output2654.1) + embedPair2542
            batchValueN02705MinusP025Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP025Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP025Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP025Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP025Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP025Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP025Output2654, pairMagnitude2542]

def batchValueN02705MinusP026Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP026Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP026Output2654.1‖ ≤ (batchValueN02705MinusP026Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP026BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP026Output2654,
    batchN02705MinusP026Center2654, batchN02705MinusP026Error2654, embedPair2542]

theorem batchValueN02705MinusP026Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP026Output2654.1) + embedPair2542
            batchValueN02705MinusP026Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP026Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP026Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP026Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP026Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP026Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP026Output2654, pairMagnitude2542]

def batchValueN02705MinusP027Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP027Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP027Output2654.1‖ ≤ (batchValueN02705MinusP027Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP027BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP027Output2654,
    batchN02705MinusP027Center2654, batchN02705MinusP027Error2654, embedPair2542]

theorem batchValueN02705MinusP027Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP027Output2654.1) + embedPair2542
            batchValueN02705MinusP027Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP027Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP027Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP027Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP027Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP027Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP027Output2654, pairMagnitude2542]

def batchValueN02705MinusP028Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP028Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP028Output2654.1‖ ≤ (batchValueN02705MinusP028Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP028BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP028Output2654,
    batchN02705MinusP028Center2654, batchN02705MinusP028Error2654, embedPair2542]

theorem batchValueN02705MinusP028Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP028Output2654.1) + embedPair2542
            batchValueN02705MinusP028Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP028Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP028Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP028Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP028Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP028Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP028Output2654, pairMagnitude2542]

def batchValueN02705MinusP029Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02705MinusP029Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP029Output2654.1‖ ≤ (batchValueN02705MinusP029Output2654.2 : ℝ)
                := by
  have h := batchN02705MinusP029BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02705MinusPosition2654, batchN02705MinusPosition2654,
      batchValueN02705MinusP029Output2654,
    batchN02705MinusP029Center2654, batchN02705MinusP029Error2654, embedPair2542]

theorem batchValueN02705MinusP029Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02705MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02705MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP029Output2654.1) + embedPair2542
            batchValueN02705MinusP029Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02705MinusPosition2654 - embedPair2542
            batchValueN02705MinusP029Output2654.1‖ + ‖embedPair2542
            batchValueN02705MinusP029Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02705MinusP029Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02705MinusP029Output2654.1 : ℝ) :=
      add_le_add batchValueN02705MinusP029Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02705MinusP029Output2654, pairMagnitude2542]

noncomputable def batchValueN02705MinusValue2654 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchValueN02705MinusP000Output2654.1
  | 1 => embedPair2542 batchValueN02705MinusP001Output2654.1
  | 2 => embedPair2542 batchValueN02705MinusP002Output2654.1
  | 3 => embedPair2542 batchValueN02705MinusP003Output2654.1
  | 4 => embedPair2542 batchValueN02705MinusP004Output2654.1
  | 5 => embedPair2542 batchValueN02705MinusP005Output2654.1
  | 6 => embedPair2542 batchValueN02705MinusP006Output2654.1
  | 7 => embedPair2542 batchValueN02705MinusP007Output2654.1
  | 8 => embedPair2542 batchValueN02705MinusP008Output2654.1
  | 9 => embedPair2542 batchValueN02705MinusP009Output2654.1
  | 10 => embedPair2542 batchValueN02705MinusP010Output2654.1
  | 11 => embedPair2542 batchValueN02705MinusP011Output2654.1
  | 12 => embedPair2542 batchValueN02705MinusP012Output2654.1
  | 13 => embedPair2542 batchValueN02705MinusP013Output2654.1
  | 14 => embedPair2542 batchValueN02705MinusP014Output2654.1
  | 15 => embedPair2542 batchValueN02705MinusP015Output2654.1
  | 16 => embedPair2542 batchValueN02705MinusP016Output2654.1
  | 17 => embedPair2542 batchValueN02705MinusP017Output2654.1
  | 18 => embedPair2542 batchValueN02705MinusP018Output2654.1
  | 19 => embedPair2542 batchValueN02705MinusP019Output2654.1
  | 20 => embedPair2542 batchValueN02705MinusP020Output2654.1
  | 21 => embedPair2542 batchValueN02705MinusP021Output2654.1
  | 22 => embedPair2542 batchValueN02705MinusP022Output2654.1
  | 23 => embedPair2542 batchValueN02705MinusP023Output2654.1
  | 24 => embedPair2542 batchValueN02705MinusP024Output2654.1
  | 25 => embedPair2542 batchValueN02705MinusP025Output2654.1
  | 26 => embedPair2542 batchValueN02705MinusP026Output2654.1
  | 27 => embedPair2542 batchValueN02705MinusP027Output2654.1
  | 28 => embedPair2542 batchValueN02705MinusP028Output2654.1
  | 29 => embedPair2542 batchValueN02705MinusP029Output2654.1
  | _ => 0

noncomputable def batchValueN02705MinusError2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (batchValueN02705MinusP000Output2654.2 : ℝ)
  | 1 => (batchValueN02705MinusP001Output2654.2 : ℝ)
  | 2 => (batchValueN02705MinusP002Output2654.2 : ℝ)
  | 3 => (batchValueN02705MinusP003Output2654.2 : ℝ)
  | 4 => (batchValueN02705MinusP004Output2654.2 : ℝ)
  | 5 => (batchValueN02705MinusP005Output2654.2 : ℝ)
  | 6 => (batchValueN02705MinusP006Output2654.2 : ℝ)
  | 7 => (batchValueN02705MinusP007Output2654.2 : ℝ)
  | 8 => (batchValueN02705MinusP008Output2654.2 : ℝ)
  | 9 => (batchValueN02705MinusP009Output2654.2 : ℝ)
  | 10 => (batchValueN02705MinusP010Output2654.2 : ℝ)
  | 11 => (batchValueN02705MinusP011Output2654.2 : ℝ)
  | 12 => (batchValueN02705MinusP012Output2654.2 : ℝ)
  | 13 => (batchValueN02705MinusP013Output2654.2 : ℝ)
  | 14 => (batchValueN02705MinusP014Output2654.2 : ℝ)
  | 15 => (batchValueN02705MinusP015Output2654.2 : ℝ)
  | 16 => (batchValueN02705MinusP016Output2654.2 : ℝ)
  | 17 => (batchValueN02705MinusP017Output2654.2 : ℝ)
  | 18 => (batchValueN02705MinusP018Output2654.2 : ℝ)
  | 19 => (batchValueN02705MinusP019Output2654.2 : ℝ)
  | 20 => (batchValueN02705MinusP020Output2654.2 : ℝ)
  | 21 => (batchValueN02705MinusP021Output2654.2 : ℝ)
  | 22 => (batchValueN02705MinusP022Output2654.2 : ℝ)
  | 23 => (batchValueN02705MinusP023Output2654.2 : ℝ)
  | 24 => (batchValueN02705MinusP024Output2654.2 : ℝ)
  | 25 => (batchValueN02705MinusP025Output2654.2 : ℝ)
  | 26 => (batchValueN02705MinusP026Output2654.2 : ℝ)
  | 27 => (batchValueN02705MinusP027Output2654.2 : ℝ)
  | 28 => (batchValueN02705MinusP028Output2654.2 : ℝ)
  | 29 => (batchValueN02705MinusP029Output2654.2 : ℝ)
  | _ => 0

theorem batchValueN02705MinusExp_error2654 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02705MinusPosition2654 -
            batchValueN02705MinusValue2654 i‖
            ≤ batchValueN02705MinusError2654 i := by
  fin_cases i
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP000Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP001Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP002Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP003Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP004Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP005Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP006Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP007Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP008Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP009Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP010Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP011Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP012Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP013Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP014Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP015Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP016Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP017Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP018Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP019Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP020Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP021Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP022Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP023Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP024Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP025Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP026Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP027Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP028Error2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP029Error2654

theorem batchValueN02705MinusUnit_norm2654 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02705MinusPosition2654‖ ≤ 1 := by
  fin_cases i
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP000Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP001Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP002Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP003Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP004Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP005Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP006Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP007Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP008Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP009Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP010Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP011Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP012Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP013Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP014Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP015Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP016Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP017Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP018Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP019Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP020Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP021Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP022Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP023Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP024Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP025Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP026Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP027Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP028Norm2654
  · simpa only [batchValueN02705MinusValue2654, batchValueN02705MinusError2654] using
      batchValueN02705MinusP029Norm2654

noncomputable def batchValueN02705MinusSumValue2654 : ℂ := ⟨(((((35838776287628633266 * 10^40
        + 6571018889414379988114950868468310127634) * 10^40
        + 2094324952666137938834698386688884785610) * 10^40
        + 3952188125641418843324001063326578990971) : ℝ) /
        (((24973988402527937851052777 * 10^40
        + 8383453304459887851413197692068732556770) * 10^40
        + 297391055812496096244882450793576927861) * 10^40
        + 5448971252983163583805434306282450321408)),
    (((((44451492468426541078 * 10^40
        + 2734603394798597630353473641095811730606) * 10^40
        + 4178710141658537875738688042034129586337) * 10^40
        + 5412947951760479060295109551099274720407) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816))⟩

noncomputable def batchValueN02705MinusUpper2654 : ℝ := ((2111 : ℝ) /
        1250000000)

theorem batchValueN02705MinusSum_eq2654 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02705MinusValue2654 i) =
      batchValueN02705MinusSumValue2654 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN02705MinusValue2654,
      batchValueN02705MinusSumValue2654, embedPair2542, batchValueN02705MinusP000Output2654,
      batchValueN02705MinusP001Output2654,
      batchValueN02705MinusP002Output2654,
      batchValueN02705MinusP003Output2654,
      batchValueN02705MinusP004Output2654,
      batchValueN02705MinusP005Output2654,
      batchValueN02705MinusP006Output2654,
      batchValueN02705MinusP007Output2654,
      batchValueN02705MinusP008Output2654,
      batchValueN02705MinusP009Output2654,
      batchValueN02705MinusP010Output2654,
      batchValueN02705MinusP011Output2654,
      batchValueN02705MinusP012Output2654,
      batchValueN02705MinusP013Output2654,
      batchValueN02705MinusP014Output2654,
      batchValueN02705MinusP015Output2654,
      batchValueN02705MinusP016Output2654,
      batchValueN02705MinusP017Output2654,
      batchValueN02705MinusP018Output2654,
      batchValueN02705MinusP019Output2654,
      batchValueN02705MinusP020Output2654,
      batchValueN02705MinusP021Output2654,
      batchValueN02705MinusP022Output2654,
      batchValueN02705MinusP023Output2654,
      batchValueN02705MinusP024Output2654,
      batchValueN02705MinusP025Output2654,
      batchValueN02705MinusP026Output2654,
      batchValueN02705MinusP027Output2654,
      batchValueN02705MinusP028Output2654,
      batchValueN02705MinusP029Output2654, Complex.mul_re, Complex.mul_im]

theorem batchValueN02705MinusSum_norm2654 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02705MinusValue2654 i‖ ≤
      ((16887 : ℝ) /
        10000000000) := by
  rw [batchValueN02705MinusSum_eq2654]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchValueN02705MinusSumValue2654]

theorem batchValueN02705MinusEvaluation_charge2654 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchValueN02705MinusError2654 i) ≤ (1 : ℝ)/10^12 :=
          by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN02705MinusError2654,
      batchValueN02705MinusP000Output2654,
      batchValueN02705MinusP001Output2654,
      batchValueN02705MinusP002Output2654,
      batchValueN02705MinusP003Output2654,
      batchValueN02705MinusP004Output2654,
      batchValueN02705MinusP005Output2654,
      batchValueN02705MinusP006Output2654,
      batchValueN02705MinusP007Output2654,
      batchValueN02705MinusP008Output2654,
      batchValueN02705MinusP009Output2654,
      batchValueN02705MinusP010Output2654,
      batchValueN02705MinusP011Output2654,
      batchValueN02705MinusP012Output2654,
      batchValueN02705MinusP013Output2654,
      batchValueN02705MinusP014Output2654,
      batchValueN02705MinusP015Output2654,
      batchValueN02705MinusP016Output2654,
      batchValueN02705MinusP017Output2654,
      batchValueN02705MinusP018Output2654,
      batchValueN02705MinusP019Output2654,
      batchValueN02705MinusP020Output2654,
      batchValueN02705MinusP021Output2654,
      batchValueN02705MinusP022Output2654,
      batchValueN02705MinusP023Output2654,
      batchValueN02705MinusP024Output2654,
      batchValueN02705MinusP025Output2654,
      batchValueN02705MinusP026Output2654,
      batchValueN02705MinusP027Output2654,
      batchValueN02705MinusP028Output2654,
      batchValueN02705MinusP029Output2654]

theorem batchValueN02705MinusSigned_le2654 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchValueN02705MinusPosition2654 ≤ batchValueN02705MinusUpper2654 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02705MinusPosition2654‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02705MinusValue2654 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchValueN02705MinusError2654 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (batchValueN02705MinusExp_error2654 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02705MinusPosition2654‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchValueN02705MinusUnit_norm2654 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02705MinusPosition2654‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchValueN02705MinusUpper2654
  linarith [batchValueN02705MinusSum_norm2654, batchValueN02705MinusEvaluation_charge2654]

theorem batchValueN02705MinusPhysical_le2654 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 batchValueN02705MinusPosition2654‖ ≤
      batchValueN02705MinusUpper2654 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchValueN02705MinusPosition2654
  simpa only [iteratedDeriv_zero] using h.trans batchValueN02705MinusSigned_le2654

theorem batchValueN02705MinusGrid2654 :
    -stripRadius2303 + (2705 : ℝ)*(2*stripRadius2303/10240) = batchValueN02705MinusPosition2654 :=
        by
  norm_num [stripRadius2303, batchValueN02705MinusPosition2654]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchValueN02705MinusSigned_le2654
#print axioms ConnesWeilRH.Dev.batchValueN02705MinusPhysical_le2654
