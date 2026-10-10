import ConnesWeilRH.Dev.C1RouteABatchN02703Plus2654
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchValueN02703PlusPosition2654 : ℝ := (((-158400514417) : ℝ) /
        51200000000)

def batchValueN02703PlusP000Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem batchValueN02703PlusP000Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP000Output2654.1‖ ≤ (batchValueN02703PlusP000Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP000BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP000Output2654,
    batchN02703PlusP000Center2654, batchN02703PlusP000Error2654, embedPair2542]

theorem batchValueN02703PlusP000Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP000Output2654.1) + embedPair2542
            batchValueN02703PlusP000Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP000Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP000Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP000Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP000Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP000Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP000Output2654, pairMagnitude2542]

def batchValueN02703PlusP001Output2654 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP001Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP001Output2654.1‖ ≤ (batchValueN02703PlusP001Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP001BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP001Output2654,
    batchN02703PlusP001Center2654, batchN02703PlusP001Error2654, embedPair2542]

theorem batchValueN02703PlusP001Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP001Output2654.1) + embedPair2542
            batchValueN02703PlusP001Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP001Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP001Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP001Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP001Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP001Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP001Output2654, pairMagnitude2542]

def batchValueN02703PlusP002Output2654 : RatState2542 :=
  (((((-315978186676346367273) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-298827836871563509461) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((2549234199278350865 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP002Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP002Output2654.1‖ ≤ (batchValueN02703PlusP002Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP002BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP002Output2654,
    batchN02703PlusP002Center2654, batchN02703PlusP002Error2654, embedPair2542]

theorem batchValueN02703PlusP002Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP002Output2654.1) + embedPair2542
            batchValueN02703PlusP002Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP002Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP002Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP002Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP002Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP002Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP002Output2654, pairMagnitude2542]

def batchValueN02703PlusP003Output2654 : RatState2542 :=
  (((((-1268809181176912783519253083) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    (((-9599536145252764711420508941) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((19188053210732762782261105 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN02703PlusP003Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP003Output2654.1‖ ≤ (batchValueN02703PlusP003Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP003BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP003Output2654,
    batchN02703PlusP003Center2654, batchN02703PlusP003Error2654, embedPair2542]

theorem batchValueN02703PlusP003Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP003Output2654.1) + embedPair2542
            batchValueN02703PlusP003Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP003Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP003Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP003Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP003Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP003Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP003Output2654, pairMagnitude2542]

def batchValueN02703PlusP004Output2654 : RatState2542 :=
  (((((-312386221358806970386657117599) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((2363446661405167442454675371511 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((288197090536147820321281271 : ℚ) /
        (2510840694154672305 * 10^40
        + 5343157692830665664409421777856138051584)))

theorem batchValueN02703PlusP004Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP004Output2654.1‖ ≤ (batchValueN02703PlusP004Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP004BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP004Output2654,
    batchN02703PlusP004Center2654, batchN02703PlusP004Error2654, embedPair2542]

theorem batchValueN02703PlusP004Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP004Output2654.1) + embedPair2542
            batchValueN02703PlusP004Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP004Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP004Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP004Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP004Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP004Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP004Output2654, pairMagnitude2542]

def batchValueN02703PlusP005Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem batchValueN02703PlusP005Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP005Output2654.1‖ ≤ (batchValueN02703PlusP005Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP005BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP005Output2654,
    batchN02703PlusP005Center2654, batchN02703PlusP005Error2654, embedPair2542]

theorem batchValueN02703PlusP005Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP005Output2654.1) + embedPair2542
            batchValueN02703PlusP005Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP005Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP005Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP005Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP005Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP005Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP005Output2654, pairMagnitude2542]

def batchValueN02703PlusP006Output2654 : RatState2542 :=
  ((((582152360891653 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((2496231124509 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP006Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP006Output2654.1‖ ≤ (batchValueN02703PlusP006Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP006BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP006Output2654,
    batchN02703PlusP006Center2654, batchN02703PlusP006Error2654, embedPair2542]

theorem batchValueN02703PlusP006Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP006Output2654.1) + embedPair2542
            batchValueN02703PlusP006Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP006Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP006Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP006Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP006Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP006Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP006Output2654, pairMagnitude2542]

def batchValueN02703PlusP007Output2654 : RatState2542 :=
  ((((5429298343613002153233162827 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((1576411260228435144735031 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP007Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP007Output2654.1‖ ≤ (batchValueN02703PlusP007Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP007BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP007Output2654,
    batchN02703PlusP007Center2654, batchN02703PlusP007Error2654, embedPair2542]

theorem batchValueN02703PlusP007Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP007Output2654.1) + embedPair2542
            batchValueN02703PlusP007Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP007Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP007Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP007Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP007Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP007Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP007Output2654, pairMagnitude2542]

def batchValueN02703PlusP008Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP008Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP008Output2654.1‖ ≤ (batchValueN02703PlusP008Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP008BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP008Output2654,
    batchN02703PlusP008Center2654, batchN02703PlusP008Error2654, embedPair2542]

theorem batchValueN02703PlusP008Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP008Output2654.1) + embedPair2542
            batchValueN02703PlusP008Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP008Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP008Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP008Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP008Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP008Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP008Output2654, pairMagnitude2542]

def batchValueN02703PlusP009Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP009Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP009Output2654.1‖ ≤ (batchValueN02703PlusP009Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP009BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP009Output2654,
    batchN02703PlusP009Center2654, batchN02703PlusP009Error2654, embedPair2542]

theorem batchValueN02703PlusP009Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP009Output2654.1) + embedPair2542
            batchValueN02703PlusP009Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP009Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP009Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP009Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP009Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP009Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP009Output2654, pairMagnitude2542]

def batchValueN02703PlusP010Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP010Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP010Output2654.1‖ ≤ (batchValueN02703PlusP010Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP010BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP010Output2654,
    batchN02703PlusP010Center2654, batchN02703PlusP010Error2654, embedPair2542]

theorem batchValueN02703PlusP010Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP010Output2654.1) + embedPair2542
            batchValueN02703PlusP010Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP010Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP010Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP010Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP010Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP010Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP010Output2654, pairMagnitude2542]

def batchValueN02703PlusP011Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP011Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP011Output2654.1‖ ≤ (batchValueN02703PlusP011Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP011BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP011Output2654,
    batchN02703PlusP011Center2654, batchN02703PlusP011Error2654, embedPair2542]

theorem batchValueN02703PlusP011Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP011Output2654.1) + embedPair2542
            batchValueN02703PlusP011Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP011Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP011Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP011Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP011Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP011Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP011Output2654, pairMagnitude2542]

def batchValueN02703PlusP012Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP012Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP012Output2654.1‖ ≤ (batchValueN02703PlusP012Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP012BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP012Output2654,
    batchN02703PlusP012Center2654, batchN02703PlusP012Error2654, embedPair2542]

theorem batchValueN02703PlusP012Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP012Output2654.1) + embedPair2542
            batchValueN02703PlusP012Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP012Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP012Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP012Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP012Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP012Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP012Output2654, pairMagnitude2542]

def batchValueN02703PlusP013Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP013Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP013Output2654.1‖ ≤ (batchValueN02703PlusP013Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP013BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP013Output2654,
    batchN02703PlusP013Center2654, batchN02703PlusP013Error2654, embedPair2542]

theorem batchValueN02703PlusP013Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP013Output2654.1) + embedPair2542
            batchValueN02703PlusP013Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP013Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP013Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP013Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP013Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP013Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP013Output2654, pairMagnitude2542]

def batchValueN02703PlusP014Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP014Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP014Output2654.1‖ ≤ (batchValueN02703PlusP014Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP014BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP014Output2654,
    batchN02703PlusP014Center2654, batchN02703PlusP014Error2654, embedPair2542]

theorem batchValueN02703PlusP014Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP014Output2654.1) + embedPair2542
            batchValueN02703PlusP014Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP014Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP014Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP014Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP014Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP014Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP014Output2654, pairMagnitude2542]

def batchValueN02703PlusP015Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP015Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP015Output2654.1‖ ≤ (batchValueN02703PlusP015Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP015BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP015Output2654,
    batchN02703PlusP015Center2654, batchN02703PlusP015Error2654, embedPair2542]

theorem batchValueN02703PlusP015Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP015Output2654.1) + embedPair2542
            batchValueN02703PlusP015Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP015Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP015Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP015Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP015Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP015Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP015Output2654, pairMagnitude2542]

def batchValueN02703PlusP016Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP016Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP016Output2654.1‖ ≤ (batchValueN02703PlusP016Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP016BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP016Output2654,
    batchN02703PlusP016Center2654, batchN02703PlusP016Error2654, embedPair2542]

theorem batchValueN02703PlusP016Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP016Output2654.1) + embedPair2542
            batchValueN02703PlusP016Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP016Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP016Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP016Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP016Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP016Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP016Output2654, pairMagnitude2542]

def batchValueN02703PlusP017Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP017Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP017Output2654.1‖ ≤ (batchValueN02703PlusP017Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP017BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP017Output2654,
    batchN02703PlusP017Center2654, batchN02703PlusP017Error2654, embedPair2542]

theorem batchValueN02703PlusP017Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP017Output2654.1) + embedPair2542
            batchValueN02703PlusP017Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP017Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP017Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP017Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP017Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP017Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP017Output2654, pairMagnitude2542]

def batchValueN02703PlusP018Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP018Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP018Output2654.1‖ ≤ (batchValueN02703PlusP018Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP018BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP018Output2654,
    batchN02703PlusP018Center2654, batchN02703PlusP018Error2654, embedPair2542]

theorem batchValueN02703PlusP018Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP018Output2654.1) + embedPair2542
            batchValueN02703PlusP018Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP018Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP018Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP018Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP018Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP018Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP018Output2654, pairMagnitude2542]

def batchValueN02703PlusP019Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP019Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP019Output2654.1‖ ≤ (batchValueN02703PlusP019Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP019BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP019Output2654,
    batchN02703PlusP019Center2654, batchN02703PlusP019Error2654, embedPair2542]

theorem batchValueN02703PlusP019Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP019Output2654.1) + embedPair2542
            batchValueN02703PlusP019Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP019Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP019Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP019Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP019Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP019Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP019Output2654, pairMagnitude2542]

def batchValueN02703PlusP020Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP020Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP020Output2654.1‖ ≤ (batchValueN02703PlusP020Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP020BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP020Output2654,
    batchN02703PlusP020Center2654, batchN02703PlusP020Error2654, embedPair2542]

theorem batchValueN02703PlusP020Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP020Output2654.1) + embedPair2542
            batchValueN02703PlusP020Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP020Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP020Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP020Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP020Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP020Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP020Output2654, pairMagnitude2542]

def batchValueN02703PlusP021Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP021Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP021Output2654.1‖ ≤ (batchValueN02703PlusP021Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP021BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP021Output2654,
    batchN02703PlusP021Center2654, batchN02703PlusP021Error2654, embedPair2542]

theorem batchValueN02703PlusP021Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP021Output2654.1) + embedPair2542
            batchValueN02703PlusP021Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP021Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP021Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP021Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP021Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP021Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP021Output2654, pairMagnitude2542]

def batchValueN02703PlusP022Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP022Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP022Output2654.1‖ ≤ (batchValueN02703PlusP022Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP022BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP022Output2654,
    batchN02703PlusP022Center2654, batchN02703PlusP022Error2654, embedPair2542]

theorem batchValueN02703PlusP022Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP022Output2654.1) + embedPair2542
            batchValueN02703PlusP022Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP022Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP022Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP022Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP022Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP022Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP022Output2654, pairMagnitude2542]

def batchValueN02703PlusP023Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP023Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP023Output2654.1‖ ≤ (batchValueN02703PlusP023Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP023BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP023Output2654,
    batchN02703PlusP023Center2654, batchN02703PlusP023Error2654, embedPair2542]

theorem batchValueN02703PlusP023Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP023Output2654.1) + embedPair2542
            batchValueN02703PlusP023Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP023Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP023Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP023Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP023Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP023Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP023Output2654, pairMagnitude2542]

def batchValueN02703PlusP024Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP024Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP024Output2654.1‖ ≤ (batchValueN02703PlusP024Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP024BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP024Output2654,
    batchN02703PlusP024Center2654, batchN02703PlusP024Error2654, embedPair2542]

theorem batchValueN02703PlusP024Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP024Output2654.1) + embedPair2542
            batchValueN02703PlusP024Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP024Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP024Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP024Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP024Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP024Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP024Output2654, pairMagnitude2542]

def batchValueN02703PlusP025Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP025Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP025Output2654.1‖ ≤ (batchValueN02703PlusP025Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP025BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP025Output2654,
    batchN02703PlusP025Center2654, batchN02703PlusP025Error2654, embedPair2542]

theorem batchValueN02703PlusP025Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP025Output2654.1) + embedPair2542
            batchValueN02703PlusP025Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP025Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP025Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP025Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP025Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP025Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP025Output2654, pairMagnitude2542]

def batchValueN02703PlusP026Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP026Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP026Output2654.1‖ ≤ (batchValueN02703PlusP026Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP026BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP026Output2654,
    batchN02703PlusP026Center2654, batchN02703PlusP026Error2654, embedPair2542]

theorem batchValueN02703PlusP026Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP026Output2654.1) + embedPair2542
            batchValueN02703PlusP026Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP026Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP026Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP026Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP026Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP026Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP026Output2654, pairMagnitude2542]

def batchValueN02703PlusP027Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP027Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP027Output2654.1‖ ≤ (batchValueN02703PlusP027Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP027BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP027Output2654,
    batchN02703PlusP027Center2654, batchN02703PlusP027Error2654, embedPair2542]

theorem batchValueN02703PlusP027Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP027Output2654.1) + embedPair2542
            batchValueN02703PlusP027Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP027Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP027Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP027Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP027Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP027Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP027Output2654, pairMagnitude2542]

def batchValueN02703PlusP028Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP028Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP028Output2654.1‖ ≤ (batchValueN02703PlusP028Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP028BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP028Output2654,
    batchN02703PlusP028Center2654, batchN02703PlusP028Error2654, embedPair2542]

theorem batchValueN02703PlusP028Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP028Output2654.1) + embedPair2542
            batchValueN02703PlusP028Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP028Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP028Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP028Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP028Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP028Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP028Output2654, pairMagnitude2542]

def batchValueN02703PlusP029Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703PlusP029Error2654 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP029Output2654.1‖ ≤ (batchValueN02703PlusP029Output2654.2 : ℝ) :=
                by
  have h := batchN02703PlusP029BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703PlusPosition2654, batchN02703PlusPosition2654,
      batchValueN02703PlusP029Output2654,
    batchN02703PlusP029Center2654, batchN02703PlusP029Error2654, embedPair2542]

theorem batchValueN02703PlusP029Norm2654 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02703PlusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02703PlusPosition2654‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP029Output2654.1) + embedPair2542
            batchValueN02703PlusP029Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02703PlusPosition2654 - embedPair2542
            batchValueN02703PlusP029Output2654.1‖ + ‖embedPair2542
            batchValueN02703PlusP029Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703PlusP029Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703PlusP029Output2654.1 : ℝ) :=
      add_le_add batchValueN02703PlusP029Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703PlusP029Output2654, pairMagnitude2542]

noncomputable def batchValueN02703PlusValue2654 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchValueN02703PlusP000Output2654.1
  | 1 => embedPair2542 batchValueN02703PlusP001Output2654.1
  | 2 => embedPair2542 batchValueN02703PlusP002Output2654.1
  | 3 => embedPair2542 batchValueN02703PlusP003Output2654.1
  | 4 => embedPair2542 batchValueN02703PlusP004Output2654.1
  | 5 => embedPair2542 batchValueN02703PlusP005Output2654.1
  | 6 => embedPair2542 batchValueN02703PlusP006Output2654.1
  | 7 => embedPair2542 batchValueN02703PlusP007Output2654.1
  | 8 => embedPair2542 batchValueN02703PlusP008Output2654.1
  | 9 => embedPair2542 batchValueN02703PlusP009Output2654.1
  | 10 => embedPair2542 batchValueN02703PlusP010Output2654.1
  | 11 => embedPair2542 batchValueN02703PlusP011Output2654.1
  | 12 => embedPair2542 batchValueN02703PlusP012Output2654.1
  | 13 => embedPair2542 batchValueN02703PlusP013Output2654.1
  | 14 => embedPair2542 batchValueN02703PlusP014Output2654.1
  | 15 => embedPair2542 batchValueN02703PlusP015Output2654.1
  | 16 => embedPair2542 batchValueN02703PlusP016Output2654.1
  | 17 => embedPair2542 batchValueN02703PlusP017Output2654.1
  | 18 => embedPair2542 batchValueN02703PlusP018Output2654.1
  | 19 => embedPair2542 batchValueN02703PlusP019Output2654.1
  | 20 => embedPair2542 batchValueN02703PlusP020Output2654.1
  | 21 => embedPair2542 batchValueN02703PlusP021Output2654.1
  | 22 => embedPair2542 batchValueN02703PlusP022Output2654.1
  | 23 => embedPair2542 batchValueN02703PlusP023Output2654.1
  | 24 => embedPair2542 batchValueN02703PlusP024Output2654.1
  | 25 => embedPair2542 batchValueN02703PlusP025Output2654.1
  | 26 => embedPair2542 batchValueN02703PlusP026Output2654.1
  | 27 => embedPair2542 batchValueN02703PlusP027Output2654.1
  | 28 => embedPair2542 batchValueN02703PlusP028Output2654.1
  | 29 => embedPair2542 batchValueN02703PlusP029Output2654.1
  | _ => 0

noncomputable def batchValueN02703PlusError2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (batchValueN02703PlusP000Output2654.2 : ℝ)
  | 1 => (batchValueN02703PlusP001Output2654.2 : ℝ)
  | 2 => (batchValueN02703PlusP002Output2654.2 : ℝ)
  | 3 => (batchValueN02703PlusP003Output2654.2 : ℝ)
  | 4 => (batchValueN02703PlusP004Output2654.2 : ℝ)
  | 5 => (batchValueN02703PlusP005Output2654.2 : ℝ)
  | 6 => (batchValueN02703PlusP006Output2654.2 : ℝ)
  | 7 => (batchValueN02703PlusP007Output2654.2 : ℝ)
  | 8 => (batchValueN02703PlusP008Output2654.2 : ℝ)
  | 9 => (batchValueN02703PlusP009Output2654.2 : ℝ)
  | 10 => (batchValueN02703PlusP010Output2654.2 : ℝ)
  | 11 => (batchValueN02703PlusP011Output2654.2 : ℝ)
  | 12 => (batchValueN02703PlusP012Output2654.2 : ℝ)
  | 13 => (batchValueN02703PlusP013Output2654.2 : ℝ)
  | 14 => (batchValueN02703PlusP014Output2654.2 : ℝ)
  | 15 => (batchValueN02703PlusP015Output2654.2 : ℝ)
  | 16 => (batchValueN02703PlusP016Output2654.2 : ℝ)
  | 17 => (batchValueN02703PlusP017Output2654.2 : ℝ)
  | 18 => (batchValueN02703PlusP018Output2654.2 : ℝ)
  | 19 => (batchValueN02703PlusP019Output2654.2 : ℝ)
  | 20 => (batchValueN02703PlusP020Output2654.2 : ℝ)
  | 21 => (batchValueN02703PlusP021Output2654.2 : ℝ)
  | 22 => (batchValueN02703PlusP022Output2654.2 : ℝ)
  | 23 => (batchValueN02703PlusP023Output2654.2 : ℝ)
  | 24 => (batchValueN02703PlusP024Output2654.2 : ℝ)
  | 25 => (batchValueN02703PlusP025Output2654.2 : ℝ)
  | 26 => (batchValueN02703PlusP026Output2654.2 : ℝ)
  | 27 => (batchValueN02703PlusP027Output2654.2 : ℝ)
  | 28 => (batchValueN02703PlusP028Output2654.2 : ℝ)
  | 29 => (batchValueN02703PlusP029Output2654.2 : ℝ)
  | _ => 0

theorem batchValueN02703PlusExp_error2654 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02703PlusPosition2654 - batchValueN02703PlusValue2654
            i‖ ≤
            batchValueN02703PlusError2654 i := by
  fin_cases i
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP000Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP001Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP002Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP003Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP004Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP005Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP006Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP007Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP008Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP009Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP010Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP011Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP012Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP013Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP014Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP015Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP016Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP017Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP018Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP019Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP020Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP021Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP022Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP023Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP024Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP025Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP026Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP027Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP028Error2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP029Error2654

theorem batchValueN02703PlusUnit_norm2654 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02703PlusPosition2654‖ ≤ 1 := by
  fin_cases i
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP000Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP001Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP002Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP003Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP004Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP005Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP006Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP007Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP008Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP009Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP010Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP011Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP012Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP013Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP014Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP015Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP016Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP017Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP018Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP019Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP020Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP021Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP022Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP023Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP024Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP025Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP026Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP027Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP028Norm2654
  · simpa only [batchValueN02703PlusValue2654, batchValueN02703PlusError2654] using
      batchValueN02703PlusP029Norm2654

noncomputable def batchValueN02703PlusSumValue2654 : ℂ := ⟨(((((1834689480482969904 * 10^40
        + 1677617303622360200578446879224112953240) * 10^40
        + 9053517447733205414406870957217412948555) * 10^40
        + 7676981473651634360585711611276179784733) : ℝ) /
        (((24973988402527937851052777 * 10^40
        + 8383453304459887851413197692068732556770) * 10^40
        + 297391055812496096244882450793576927861) * 10^40
        + 5448971252983163583805434306282450321408)),
    (((((1841325739213522053 * 10^40
        + 6858036655816029363345898794705119554967) * 10^40
        + 8502341458881485608522584808033509711036) * 10^40
        + 4411131558532774960220055375539364753517) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816))⟩

noncomputable def batchValueN02703PlusUpper2654 : ℝ := ((823 : ℝ) /
        10000000000)

theorem batchValueN02703PlusSum_eq2654 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02703PlusValue2654 i) =
      batchValueN02703PlusSumValue2654 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN02703PlusValue2654,
      batchValueN02703PlusSumValue2654, embedPair2542, batchValueN02703PlusP000Output2654,
      batchValueN02703PlusP001Output2654,
      batchValueN02703PlusP002Output2654,
      batchValueN02703PlusP003Output2654,
      batchValueN02703PlusP004Output2654,
      batchValueN02703PlusP005Output2654,
      batchValueN02703PlusP006Output2654,
      batchValueN02703PlusP007Output2654,
      batchValueN02703PlusP008Output2654,
      batchValueN02703PlusP009Output2654,
      batchValueN02703PlusP010Output2654,
      batchValueN02703PlusP011Output2654,
      batchValueN02703PlusP012Output2654,
      batchValueN02703PlusP013Output2654,
      batchValueN02703PlusP014Output2654,
      batchValueN02703PlusP015Output2654,
      batchValueN02703PlusP016Output2654,
      batchValueN02703PlusP017Output2654,
      batchValueN02703PlusP018Output2654,
      batchValueN02703PlusP019Output2654,
      batchValueN02703PlusP020Output2654,
      batchValueN02703PlusP021Output2654,
      batchValueN02703PlusP022Output2654,
      batchValueN02703PlusP023Output2654,
      batchValueN02703PlusP024Output2654,
      batchValueN02703PlusP025Output2654,
      batchValueN02703PlusP026Output2654,
      batchValueN02703PlusP027Output2654,
      batchValueN02703PlusP028Output2654,
      batchValueN02703PlusP029Output2654, Complex.mul_re, Complex.mul_im]

theorem batchValueN02703PlusSum_norm2654 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02703PlusValue2654 i‖ ≤
      ((411 : ℝ) /
        5000000000) := by
  rw [batchValueN02703PlusSum_eq2654]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchValueN02703PlusSumValue2654]

theorem batchValueN02703PlusEvaluation_charge2654 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchValueN02703PlusError2654 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN02703PlusError2654,
      batchValueN02703PlusP000Output2654,
      batchValueN02703PlusP001Output2654,
      batchValueN02703PlusP002Output2654,
      batchValueN02703PlusP003Output2654,
      batchValueN02703PlusP004Output2654,
      batchValueN02703PlusP005Output2654,
      batchValueN02703PlusP006Output2654,
      batchValueN02703PlusP007Output2654,
      batchValueN02703PlusP008Output2654,
      batchValueN02703PlusP009Output2654,
      batchValueN02703PlusP010Output2654,
      batchValueN02703PlusP011Output2654,
      batchValueN02703PlusP012Output2654,
      batchValueN02703PlusP013Output2654,
      batchValueN02703PlusP014Output2654,
      batchValueN02703PlusP015Output2654,
      batchValueN02703PlusP016Output2654,
      batchValueN02703PlusP017Output2654,
      batchValueN02703PlusP018Output2654,
      batchValueN02703PlusP019Output2654,
      batchValueN02703PlusP020Output2654,
      batchValueN02703PlusP021Output2654,
      batchValueN02703PlusP022Output2654,
      batchValueN02703PlusP023Output2654,
      batchValueN02703PlusP024Output2654,
      batchValueN02703PlusP025Output2654,
      batchValueN02703PlusP026Output2654,
      batchValueN02703PlusP027Output2654,
      batchValueN02703PlusP028Output2654,
      batchValueN02703PlusP029Output2654]

theorem batchValueN02703PlusSigned_le2654 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchValueN02703PlusPosition2654 ≤ batchValueN02703PlusUpper2654 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02703PlusPosition2654‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02703PlusValue2654 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchValueN02703PlusError2654 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (batchValueN02703PlusExp_error2654 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02703PlusPosition2654‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchValueN02703PlusUnit_norm2654 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN02703PlusPosition2654‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchValueN02703PlusUpper2654
  linarith [batchValueN02703PlusSum_norm2654, batchValueN02703PlusEvaluation_charge2654]

theorem batchValueN02703PlusPhysical_le2654 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 batchValueN02703PlusPosition2654‖ ≤
      batchValueN02703PlusUpper2654 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchValueN02703PlusPosition2654
  simpa only [iteratedDeriv_zero] using h.trans batchValueN02703PlusSigned_le2654

theorem batchValueN02703PlusGrid2654 :
    -stripRadius2303 + (2703 : ℝ)*(2*stripRadius2303/10240) = batchValueN02703PlusPosition2654 :=
        by
  norm_num [stripRadius2303, batchValueN02703PlusPosition2654]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchValueN02703PlusSigned_le2654
#print axioms ConnesWeilRH.Dev.batchValueN02703PlusPhysical_le2654
