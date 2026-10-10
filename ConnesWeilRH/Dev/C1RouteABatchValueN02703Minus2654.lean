import ConnesWeilRH.Dev.C1RouteABatchN02703Minus2654
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchValueN02703MinusPosition2654 : ℝ := (((-158400514417) : ℝ) /
        51200000000)

def batchValueN02703MinusP000Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem batchValueN02703MinusP000Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP000Output2654.1‖ ≤ (batchValueN02703MinusP000Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP000BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP000Output2654,
    batchN02703MinusP000Center2654, batchN02703MinusP000Error2654, embedPair2542]

theorem batchValueN02703MinusP000Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP000Output2654.1) + embedPair2542
            batchValueN02703MinusP000Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP000Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP000Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP000Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP000Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP000Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP000Output2654, pairMagnitude2542]

def batchValueN02703MinusP001Output2654 : RatState2542 :=
  (((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP001Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP001Output2654.1‖ ≤ (batchValueN02703MinusP001Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP001BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP001Output2654,
    batchN02703MinusP001Center2654, batchN02703MinusP001Error2654, embedPair2542]

theorem batchValueN02703MinusP001Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP001Output2654.1) + embedPair2542
            batchValueN02703MinusP001Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP001Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP001Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP001Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP001Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP001Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP001Output2654, pairMagnitude2542]

def batchValueN02703MinusP002Output2654 : RatState2542 :=
  (((((-6970437208017745221721) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-1648025687177071950569) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))),
    ((13890051478555904937 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN02703MinusP002Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP002Output2654.1‖ ≤ (batchValueN02703MinusP002Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP002BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP002Output2654,
    batchN02703MinusP002Center2654, batchN02703MinusP002Error2654, embedPair2542]

theorem batchValueN02703MinusP002Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP002Output2654.1) + embedPair2542
            batchValueN02703MinusP002Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP002Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP002Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP002Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP002Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP002Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP002Output2654, pairMagnitude2542]

def batchValueN02703MinusP003Output2654 : RatState2542 :=
  (((((-111959054128113850382852145511) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-52941125960634317898434698617) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((836402606886840621453327411 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP003Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP003Output2654.1‖ ≤ (batchValueN02703MinusP003Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP003BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP003Output2654,
    batchN02703MinusP003Center2654, batchN02703MinusP003Error2654, embedPair2542]

theorem batchValueN02703MinusP003Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP003Output2654.1) + embedPair2542
            batchValueN02703MinusP003Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP003Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP003Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP003Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP003Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP003Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP003Output2654, pairMagnitude2542]

def batchValueN02703MinusP004Output2654 : RatState2542 :=
  (((((-55129591407190581895480487846843) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((26068661133083737741581242579421 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((401998131106820665747522716369 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP004Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP004Output2654.1‖ ≤ (batchValueN02703MinusP004Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP004BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP004Output2654,
    batchN02703MinusP004Center2654, batchN02703MinusP004Error2654, embedPair2542]

theorem batchValueN02703MinusP004Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP004Output2654.1) + embedPair2542
            batchValueN02703MinusP004Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP004Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP004Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP004Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP004Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP004Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP004Output2654, pairMagnitude2542]

def batchValueN02703MinusP005Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((0 : ℚ) /
        1))

theorem batchValueN02703MinusP005Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP005Output2654.1‖ ≤ (batchValueN02703MinusP005Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP005BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP005Output2654,
    batchN02703MinusP005Center2654, batchN02703MinusP005Error2654, embedPair2542]

theorem batchValueN02703MinusP005Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP005Output2654.1) + embedPair2542
            batchValueN02703MinusP005Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP005Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP005Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP005Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP005Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP005Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP005Output2654, pairMagnitude2542]

def batchValueN02703MinusP006Output2654 : RatState2542 :=
  ((((25684408913017653 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((4299411043621 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN02703MinusP006Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP006Output2654.1‖ ≤ (batchValueN02703MinusP006Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP006BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP006Output2654,
    batchN02703MinusP006Center2654, batchN02703MinusP006Error2654, embedPair2542]

theorem batchValueN02703MinusP006Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP006Output2654.1) + embedPair2542
            batchValueN02703MinusP006Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP006Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP006Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP006Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP006Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP006Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP006Output2654, pairMagnitude2542]

def batchValueN02703MinusP007Output2654 : RatState2542 :=
  ((((29942401709609983149248847675 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1)),
    ((8283591204048782430816091 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN02703MinusP007Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP007Output2654.1‖ ≤ (batchValueN02703MinusP007Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP007BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP007Output2654,
    batchN02703MinusP007Center2654, batchN02703MinusP007Error2654, embedPair2542]

theorem batchValueN02703MinusP007Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP007Output2654.1) + embedPair2542
            batchValueN02703MinusP007Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP007Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP007Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP007Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP007Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP007Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP007Output2654, pairMagnitude2542]

def batchValueN02703MinusP008Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP008Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP008Output2654.1‖ ≤ (batchValueN02703MinusP008Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP008BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP008Output2654,
    batchN02703MinusP008Center2654, batchN02703MinusP008Error2654, embedPair2542]

theorem batchValueN02703MinusP008Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP008Output2654.1) + embedPair2542
            batchValueN02703MinusP008Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP008Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP008Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP008Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP008Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP008Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP008Output2654, pairMagnitude2542]

def batchValueN02703MinusP009Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP009Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP009Output2654.1‖ ≤ (batchValueN02703MinusP009Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP009BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP009Output2654,
    batchN02703MinusP009Center2654, batchN02703MinusP009Error2654, embedPair2542]

theorem batchValueN02703MinusP009Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP009Output2654.1) + embedPair2542
            batchValueN02703MinusP009Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP009Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP009Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP009Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP009Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP009Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP009Output2654, pairMagnitude2542]

def batchValueN02703MinusP010Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP010Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP010Output2654.1‖ ≤ (batchValueN02703MinusP010Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP010BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP010Output2654,
    batchN02703MinusP010Center2654, batchN02703MinusP010Error2654, embedPair2542]

theorem batchValueN02703MinusP010Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP010Output2654.1) + embedPair2542
            batchValueN02703MinusP010Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP010Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP010Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP010Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP010Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP010Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP010Output2654, pairMagnitude2542]

def batchValueN02703MinusP011Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP011Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP011Output2654.1‖ ≤ (batchValueN02703MinusP011Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP011BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP011Output2654,
    batchN02703MinusP011Center2654, batchN02703MinusP011Error2654, embedPair2542]

theorem batchValueN02703MinusP011Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP011Output2654.1) + embedPair2542
            batchValueN02703MinusP011Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP011Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP011Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP011Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP011Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP011Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP011Output2654, pairMagnitude2542]

def batchValueN02703MinusP012Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP012Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP012Output2654.1‖ ≤ (batchValueN02703MinusP012Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP012BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP012Output2654,
    batchN02703MinusP012Center2654, batchN02703MinusP012Error2654, embedPair2542]

theorem batchValueN02703MinusP012Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP012Output2654.1) + embedPair2542
            batchValueN02703MinusP012Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP012Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP012Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP012Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP012Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP012Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP012Output2654, pairMagnitude2542]

def batchValueN02703MinusP013Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP013Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP013Output2654.1‖ ≤ (batchValueN02703MinusP013Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP013BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP013Output2654,
    batchN02703MinusP013Center2654, batchN02703MinusP013Error2654, embedPair2542]

theorem batchValueN02703MinusP013Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP013Output2654.1) + embedPair2542
            batchValueN02703MinusP013Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP013Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP013Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP013Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP013Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP013Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP013Output2654, pairMagnitude2542]

def batchValueN02703MinusP014Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP014Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP014Output2654.1‖ ≤ (batchValueN02703MinusP014Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP014BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP014Output2654,
    batchN02703MinusP014Center2654, batchN02703MinusP014Error2654, embedPair2542]

theorem batchValueN02703MinusP014Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP014Output2654.1) + embedPair2542
            batchValueN02703MinusP014Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP014Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP014Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP014Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP014Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP014Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP014Output2654, pairMagnitude2542]

def batchValueN02703MinusP015Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP015Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP015Output2654.1‖ ≤ (batchValueN02703MinusP015Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP015BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP015Output2654,
    batchN02703MinusP015Center2654, batchN02703MinusP015Error2654, embedPair2542]

theorem batchValueN02703MinusP015Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP015Output2654.1) + embedPair2542
            batchValueN02703MinusP015Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP015Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP015Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP015Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP015Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP015Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP015Output2654, pairMagnitude2542]

def batchValueN02703MinusP016Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP016Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP016Output2654.1‖ ≤ (batchValueN02703MinusP016Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP016BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP016Output2654,
    batchN02703MinusP016Center2654, batchN02703MinusP016Error2654, embedPair2542]

theorem batchValueN02703MinusP016Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP016Output2654.1) + embedPair2542
            batchValueN02703MinusP016Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP016Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP016Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP016Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP016Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP016Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP016Output2654, pairMagnitude2542]

def batchValueN02703MinusP017Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP017Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP017Output2654.1‖ ≤ (batchValueN02703MinusP017Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP017BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP017Output2654,
    batchN02703MinusP017Center2654, batchN02703MinusP017Error2654, embedPair2542]

theorem batchValueN02703MinusP017Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP017Output2654.1) + embedPair2542
            batchValueN02703MinusP017Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP017Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP017Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP017Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP017Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP017Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP017Output2654, pairMagnitude2542]

def batchValueN02703MinusP018Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP018Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP018Output2654.1‖ ≤ (batchValueN02703MinusP018Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP018BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP018Output2654,
    batchN02703MinusP018Center2654, batchN02703MinusP018Error2654, embedPair2542]

theorem batchValueN02703MinusP018Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP018Output2654.1) + embedPair2542
            batchValueN02703MinusP018Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP018Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP018Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP018Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP018Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP018Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP018Output2654, pairMagnitude2542]

def batchValueN02703MinusP019Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP019Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP019Output2654.1‖ ≤ (batchValueN02703MinusP019Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP019BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP019Output2654,
    batchN02703MinusP019Center2654, batchN02703MinusP019Error2654, embedPair2542]

theorem batchValueN02703MinusP019Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP019Output2654.1) + embedPair2542
            batchValueN02703MinusP019Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP019Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP019Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP019Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP019Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP019Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP019Output2654, pairMagnitude2542]

def batchValueN02703MinusP020Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP020Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP020Output2654.1‖ ≤ (batchValueN02703MinusP020Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP020BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP020Output2654,
    batchN02703MinusP020Center2654, batchN02703MinusP020Error2654, embedPair2542]

theorem batchValueN02703MinusP020Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP020Output2654.1) + embedPair2542
            batchValueN02703MinusP020Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP020Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP020Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP020Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP020Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP020Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP020Output2654, pairMagnitude2542]

def batchValueN02703MinusP021Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP021Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP021Output2654.1‖ ≤ (batchValueN02703MinusP021Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP021BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP021Output2654,
    batchN02703MinusP021Center2654, batchN02703MinusP021Error2654, embedPair2542]

theorem batchValueN02703MinusP021Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP021Output2654.1) + embedPair2542
            batchValueN02703MinusP021Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP021Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP021Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP021Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP021Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP021Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP021Output2654, pairMagnitude2542]

def batchValueN02703MinusP022Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP022Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP022Output2654.1‖ ≤ (batchValueN02703MinusP022Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP022BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP022Output2654,
    batchN02703MinusP022Center2654, batchN02703MinusP022Error2654, embedPair2542]

theorem batchValueN02703MinusP022Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP022Output2654.1) + embedPair2542
            batchValueN02703MinusP022Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP022Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP022Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP022Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP022Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP022Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP022Output2654, pairMagnitude2542]

def batchValueN02703MinusP023Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP023Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP023Output2654.1‖ ≤ (batchValueN02703MinusP023Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP023BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP023Output2654,
    batchN02703MinusP023Center2654, batchN02703MinusP023Error2654, embedPair2542]

theorem batchValueN02703MinusP023Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP023Output2654.1) + embedPair2542
            batchValueN02703MinusP023Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP023Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP023Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP023Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP023Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP023Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP023Output2654, pairMagnitude2542]

def batchValueN02703MinusP024Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP024Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP024Output2654.1‖ ≤ (batchValueN02703MinusP024Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP024BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP024Output2654,
    batchN02703MinusP024Center2654, batchN02703MinusP024Error2654, embedPair2542]

theorem batchValueN02703MinusP024Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP024Output2654.1) + embedPair2542
            batchValueN02703MinusP024Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP024Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP024Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP024Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP024Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP024Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP024Output2654, pairMagnitude2542]

def batchValueN02703MinusP025Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP025Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP025Output2654.1‖ ≤ (batchValueN02703MinusP025Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP025BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP025Output2654,
    batchN02703MinusP025Center2654, batchN02703MinusP025Error2654, embedPair2542]

theorem batchValueN02703MinusP025Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP025Output2654.1) + embedPair2542
            batchValueN02703MinusP025Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP025Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP025Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP025Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP025Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP025Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP025Output2654, pairMagnitude2542]

def batchValueN02703MinusP026Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP026Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP026Output2654.1‖ ≤ (batchValueN02703MinusP026Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP026BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP026Output2654,
    batchN02703MinusP026Center2654, batchN02703MinusP026Error2654, embedPair2542]

theorem batchValueN02703MinusP026Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP026Output2654.1) + embedPair2542
            batchValueN02703MinusP026Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP026Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP026Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP026Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP026Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP026Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP026Output2654, pairMagnitude2542]

def batchValueN02703MinusP027Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP027Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP027Output2654.1‖ ≤ (batchValueN02703MinusP027Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP027BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP027Output2654,
    batchN02703MinusP027Center2654, batchN02703MinusP027Error2654, embedPair2542]

theorem batchValueN02703MinusP027Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP027Output2654.1) + embedPair2542
            batchValueN02703MinusP027Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP027Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP027Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP027Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP027Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP027Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP027Output2654, pairMagnitude2542]

def batchValueN02703MinusP028Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP028Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP028Output2654.1‖ ≤ (batchValueN02703MinusP028Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP028BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP028Output2654,
    batchN02703MinusP028Center2654, batchN02703MinusP028Error2654, embedPair2542]

theorem batchValueN02703MinusP028Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP028Output2654.1) + embedPair2542
            batchValueN02703MinusP028Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP028Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP028Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP028Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP028Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP028Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP028Output2654, pairMagnitude2542]

def batchValueN02703MinusP029Output2654 : RatState2542 :=
  ((((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1)),
    ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN02703MinusP029Error2654 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP029Output2654.1‖ ≤ (batchValueN02703MinusP029Output2654.2 : ℝ)
                := by
  have h := batchN02703MinusP029BaseError2654
  convert h using 1
  all_goals norm_num [batchValueN02703MinusPosition2654, batchN02703MinusPosition2654,
      batchValueN02703MinusP029Output2654,
    batchN02703MinusP029Center2654, batchN02703MinusP029Error2654, embedPair2542]

theorem batchValueN02703MinusP029Norm2654 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02703MinusPosition2654‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02703MinusPosition2654‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP029Output2654.1) + embedPair2542
            batchValueN02703MinusP029Output2654.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN02703MinusPosition2654 - embedPair2542
            batchValueN02703MinusP029Output2654.1‖ + ‖embedPair2542
            batchValueN02703MinusP029Output2654.1‖ := norm_add_le _ _
    _ ≤ (batchValueN02703MinusP029Output2654.2 : ℝ) + (pairMagnitude2542
        batchValueN02703MinusP029Output2654.1 : ℝ) :=
      add_le_add batchValueN02703MinusP029Error2654 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN02703MinusP029Output2654, pairMagnitude2542]

noncomputable def batchValueN02703MinusValue2654 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchValueN02703MinusP000Output2654.1
  | 1 => embedPair2542 batchValueN02703MinusP001Output2654.1
  | 2 => embedPair2542 batchValueN02703MinusP002Output2654.1
  | 3 => embedPair2542 batchValueN02703MinusP003Output2654.1
  | 4 => embedPair2542 batchValueN02703MinusP004Output2654.1
  | 5 => embedPair2542 batchValueN02703MinusP005Output2654.1
  | 6 => embedPair2542 batchValueN02703MinusP006Output2654.1
  | 7 => embedPair2542 batchValueN02703MinusP007Output2654.1
  | 8 => embedPair2542 batchValueN02703MinusP008Output2654.1
  | 9 => embedPair2542 batchValueN02703MinusP009Output2654.1
  | 10 => embedPair2542 batchValueN02703MinusP010Output2654.1
  | 11 => embedPair2542 batchValueN02703MinusP011Output2654.1
  | 12 => embedPair2542 batchValueN02703MinusP012Output2654.1
  | 13 => embedPair2542 batchValueN02703MinusP013Output2654.1
  | 14 => embedPair2542 batchValueN02703MinusP014Output2654.1
  | 15 => embedPair2542 batchValueN02703MinusP015Output2654.1
  | 16 => embedPair2542 batchValueN02703MinusP016Output2654.1
  | 17 => embedPair2542 batchValueN02703MinusP017Output2654.1
  | 18 => embedPair2542 batchValueN02703MinusP018Output2654.1
  | 19 => embedPair2542 batchValueN02703MinusP019Output2654.1
  | 20 => embedPair2542 batchValueN02703MinusP020Output2654.1
  | 21 => embedPair2542 batchValueN02703MinusP021Output2654.1
  | 22 => embedPair2542 batchValueN02703MinusP022Output2654.1
  | 23 => embedPair2542 batchValueN02703MinusP023Output2654.1
  | 24 => embedPair2542 batchValueN02703MinusP024Output2654.1
  | 25 => embedPair2542 batchValueN02703MinusP025Output2654.1
  | 26 => embedPair2542 batchValueN02703MinusP026Output2654.1
  | 27 => embedPair2542 batchValueN02703MinusP027Output2654.1
  | 28 => embedPair2542 batchValueN02703MinusP028Output2654.1
  | 29 => embedPair2542 batchValueN02703MinusP029Output2654.1
  | _ => 0

noncomputable def batchValueN02703MinusError2654 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (batchValueN02703MinusP000Output2654.2 : ℝ)
  | 1 => (batchValueN02703MinusP001Output2654.2 : ℝ)
  | 2 => (batchValueN02703MinusP002Output2654.2 : ℝ)
  | 3 => (batchValueN02703MinusP003Output2654.2 : ℝ)
  | 4 => (batchValueN02703MinusP004Output2654.2 : ℝ)
  | 5 => (batchValueN02703MinusP005Output2654.2 : ℝ)
  | 6 => (batchValueN02703MinusP006Output2654.2 : ℝ)
  | 7 => (batchValueN02703MinusP007Output2654.2 : ℝ)
  | 8 => (batchValueN02703MinusP008Output2654.2 : ℝ)
  | 9 => (batchValueN02703MinusP009Output2654.2 : ℝ)
  | 10 => (batchValueN02703MinusP010Output2654.2 : ℝ)
  | 11 => (batchValueN02703MinusP011Output2654.2 : ℝ)
  | 12 => (batchValueN02703MinusP012Output2654.2 : ℝ)
  | 13 => (batchValueN02703MinusP013Output2654.2 : ℝ)
  | 14 => (batchValueN02703MinusP014Output2654.2 : ℝ)
  | 15 => (batchValueN02703MinusP015Output2654.2 : ℝ)
  | 16 => (batchValueN02703MinusP016Output2654.2 : ℝ)
  | 17 => (batchValueN02703MinusP017Output2654.2 : ℝ)
  | 18 => (batchValueN02703MinusP018Output2654.2 : ℝ)
  | 19 => (batchValueN02703MinusP019Output2654.2 : ℝ)
  | 20 => (batchValueN02703MinusP020Output2654.2 : ℝ)
  | 21 => (batchValueN02703MinusP021Output2654.2 : ℝ)
  | 22 => (batchValueN02703MinusP022Output2654.2 : ℝ)
  | 23 => (batchValueN02703MinusP023Output2654.2 : ℝ)
  | 24 => (batchValueN02703MinusP024Output2654.2 : ℝ)
  | 25 => (batchValueN02703MinusP025Output2654.2 : ℝ)
  | 26 => (batchValueN02703MinusP026Output2654.2 : ℝ)
  | 27 => (batchValueN02703MinusP027Output2654.2 : ℝ)
  | 28 => (batchValueN02703MinusP028Output2654.2 : ℝ)
  | 29 => (batchValueN02703MinusP029Output2654.2 : ℝ)
  | _ => 0

theorem batchValueN02703MinusExp_error2654 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02703MinusPosition2654 -
            batchValueN02703MinusValue2654 i‖
            ≤ batchValueN02703MinusError2654 i := by
  fin_cases i
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP000Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP001Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP002Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP003Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP004Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP005Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP006Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP007Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP008Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP009Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP010Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP011Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP012Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP013Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP014Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP015Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP016Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP017Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP018Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP019Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP020Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP021Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP022Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP023Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP024Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP025Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP026Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP027Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP028Error2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP029Error2654

theorem batchValueN02703MinusUnit_norm2654 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02703MinusPosition2654‖ ≤ 1 := by
  fin_cases i
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP000Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP001Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP002Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP003Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP004Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP005Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP006Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP007Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP008Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP009Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP010Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP011Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP012Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP013Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP014Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP015Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP016Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP017Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP018Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP019Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP020Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP021Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP022Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP023Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP024Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP025Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP026Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP027Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP028Norm2654
  · simpa only [batchValueN02703MinusValue2654, batchValueN02703MinusError2654] using
      batchValueN02703MinusP029Norm2654

noncomputable def batchValueN02703MinusSumValue2654 : ℂ := ⟨(((((10118252112934995426 * 10^40
        + 5964208637168166433176771711197474031551) * 10^40
        + 7090224052715372421708897767358623258079) * 10^40
        + 6713257656343697701784435877202666369505) : ℝ) /
        (((6243497100631984462763194 * 10^40
        + 4595863326114971962853299423017183139192) * 10^40
        + 5074347763953124024061220612698394231965) * 10^40
        + 3862242813245790895951358576570612580352)),
    (((((40619403445850301678 * 10^40
        + 3542510559578175706477380042850667085743) * 10^40
        + 4235585736072508905246092434713716138915) * 10^40
        + 2816114825001106586246104411015870780521) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816))⟩

noncomputable def batchValueN02703MinusUpper2654 : ℝ := ((9067 : ℝ) /
        5000000000)

theorem batchValueN02703MinusSum_eq2654 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02703MinusValue2654 i) =
      batchValueN02703MinusSumValue2654 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN02703MinusValue2654,
      batchValueN02703MinusSumValue2654, embedPair2542, batchValueN02703MinusP000Output2654,
      batchValueN02703MinusP001Output2654,
      batchValueN02703MinusP002Output2654,
      batchValueN02703MinusP003Output2654,
      batchValueN02703MinusP004Output2654,
      batchValueN02703MinusP005Output2654,
      batchValueN02703MinusP006Output2654,
      batchValueN02703MinusP007Output2654,
      batchValueN02703MinusP008Output2654,
      batchValueN02703MinusP009Output2654,
      batchValueN02703MinusP010Output2654,
      batchValueN02703MinusP011Output2654,
      batchValueN02703MinusP012Output2654,
      batchValueN02703MinusP013Output2654,
      batchValueN02703MinusP014Output2654,
      batchValueN02703MinusP015Output2654,
      batchValueN02703MinusP016Output2654,
      batchValueN02703MinusP017Output2654,
      batchValueN02703MinusP018Output2654,
      batchValueN02703MinusP019Output2654,
      batchValueN02703MinusP020Output2654,
      batchValueN02703MinusP021Output2654,
      batchValueN02703MinusP022Output2654,
      batchValueN02703MinusP023Output2654,
      batchValueN02703MinusP024Output2654,
      batchValueN02703MinusP025Output2654,
      batchValueN02703MinusP026Output2654,
      batchValueN02703MinusP027Output2654,
      batchValueN02703MinusP028Output2654,
      batchValueN02703MinusP029Output2654, Complex.mul_re, Complex.mul_im]

theorem batchValueN02703MinusSum_norm2654 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02703MinusValue2654 i‖ ≤
      ((18133 : ℝ) /
        10000000000) := by
  rw [batchValueN02703MinusSum_eq2654]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchValueN02703MinusSumValue2654]

theorem batchValueN02703MinusEvaluation_charge2654 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchValueN02703MinusError2654 i) ≤ (1 : ℝ)/10^12 :=
          by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN02703MinusError2654,
      batchValueN02703MinusP000Output2654,
      batchValueN02703MinusP001Output2654,
      batchValueN02703MinusP002Output2654,
      batchValueN02703MinusP003Output2654,
      batchValueN02703MinusP004Output2654,
      batchValueN02703MinusP005Output2654,
      batchValueN02703MinusP006Output2654,
      batchValueN02703MinusP007Output2654,
      batchValueN02703MinusP008Output2654,
      batchValueN02703MinusP009Output2654,
      batchValueN02703MinusP010Output2654,
      batchValueN02703MinusP011Output2654,
      batchValueN02703MinusP012Output2654,
      batchValueN02703MinusP013Output2654,
      batchValueN02703MinusP014Output2654,
      batchValueN02703MinusP015Output2654,
      batchValueN02703MinusP016Output2654,
      batchValueN02703MinusP017Output2654,
      batchValueN02703MinusP018Output2654,
      batchValueN02703MinusP019Output2654,
      batchValueN02703MinusP020Output2654,
      batchValueN02703MinusP021Output2654,
      batchValueN02703MinusP022Output2654,
      batchValueN02703MinusP023Output2654,
      batchValueN02703MinusP024Output2654,
      batchValueN02703MinusP025Output2654,
      batchValueN02703MinusP026Output2654,
      batchValueN02703MinusP027Output2654,
      batchValueN02703MinusP028Output2654,
      batchValueN02703MinusP029Output2654]

theorem batchValueN02703MinusSigned_le2654 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchValueN02703MinusPosition2654 ≤ batchValueN02703MinusUpper2654 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02703MinusPosition2654‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN02703MinusValue2654 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchValueN02703MinusError2654 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (batchValueN02703MinusExp_error2654 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02703MinusPosition2654‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchValueN02703MinusUnit_norm2654 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN02703MinusPosition2654‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchValueN02703MinusUpper2654
  linarith [batchValueN02703MinusSum_norm2654, batchValueN02703MinusEvaluation_charge2654]

theorem batchValueN02703MinusPhysical_le2654 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 batchValueN02703MinusPosition2654‖ ≤
      batchValueN02703MinusUpper2654 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchValueN02703MinusPosition2654
  simpa only [iteratedDeriv_zero] using h.trans batchValueN02703MinusSigned_le2654

theorem batchValueN02703MinusGrid2654 :
    -stripRadius2303 + (2703 : ℝ)*(2*stripRadius2303/10240) = batchValueN02703MinusPosition2654 :=
        by
  norm_num [stripRadius2303, batchValueN02703MinusPosition2654]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchValueN02703MinusSigned_le2654
#print axioms ConnesWeilRH.Dev.batchValueN02703MinusPhysical_le2654
