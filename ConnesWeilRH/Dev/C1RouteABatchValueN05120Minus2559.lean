import ConnesWeilRH.Dev.C1RouteABatchN05120Minus2559
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchValueN05120MinusPosition2559 : ℝ := (0 : ℝ)

def batchValueN05120MinusP000Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP000Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP000Output2559.1‖ ≤ (batchValueN05120MinusP000Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP000BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP000Output2559,
    batchN05120MinusP000Center2559, batchN05120MinusP000Error2559, embedPair2542]

theorem batchValueN05120MinusP000Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP000Output2559.1) + embedPair2542
            batchValueN05120MinusP000Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP000Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP000Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP000Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP000Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP000Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP000Output2559, pairMagnitude2542]

def batchValueN05120MinusP001Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP001Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP001Output2559.1‖ ≤ (batchValueN05120MinusP001Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP001BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP001Output2559,
    batchN05120MinusP001Center2559, batchN05120MinusP001Error2559, embedPair2542]

theorem batchValueN05120MinusP001Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP001Output2559.1) + embedPair2542
            batchValueN05120MinusP001Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP001Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP001Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP001Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP001Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP001Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP001Output2559, pairMagnitude2542]

def batchValueN05120MinusP002Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP002Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP002Output2559.1‖ ≤ (batchValueN05120MinusP002Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP002BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP002Output2559,
    batchN05120MinusP002Center2559, batchN05120MinusP002Error2559, embedPair2542]

theorem batchValueN05120MinusP002Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP002Output2559.1) + embedPair2542
            batchValueN05120MinusP002Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP002Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP002Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP002Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP002Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP002Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP002Output2559, pairMagnitude2542]

def batchValueN05120MinusP003Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP003Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP003Output2559.1‖ ≤ (batchValueN05120MinusP003Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP003BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP003Output2559,
    batchN05120MinusP003Center2559, batchN05120MinusP003Error2559, embedPair2542]

theorem batchValueN05120MinusP003Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP003Output2559.1) + embedPair2542
            batchValueN05120MinusP003Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP003Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP003Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP003Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP003Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP003Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP003Output2559, pairMagnitude2542]

def batchValueN05120MinusP004Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP004Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP004Output2559.1‖ ≤ (batchValueN05120MinusP004Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP004BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP004Output2559,
    batchN05120MinusP004Center2559, batchN05120MinusP004Error2559, embedPair2542]

theorem batchValueN05120MinusP004Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP004Output2559.1) + embedPair2542
            batchValueN05120MinusP004Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP004Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP004Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP004Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP004Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP004Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP004Output2559, pairMagnitude2542]

def batchValueN05120MinusP005Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP005Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP005Output2559.1‖ ≤ (batchValueN05120MinusP005Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP005BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP005Output2559,
    batchN05120MinusP005Center2559, batchN05120MinusP005Error2559, embedPair2542]

theorem batchValueN05120MinusP005Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP005Output2559.1) + embedPair2542
            batchValueN05120MinusP005Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP005Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP005Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP005Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP005Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP005Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP005Output2559, pairMagnitude2542]

def batchValueN05120MinusP006Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP006Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP006Output2559.1‖ ≤ (batchValueN05120MinusP006Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP006BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP006Output2559,
    batchN05120MinusP006Center2559, batchN05120MinusP006Error2559, embedPair2542]

theorem batchValueN05120MinusP006Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP006Output2559.1) + embedPair2542
            batchValueN05120MinusP006Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP006Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP006Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP006Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP006Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP006Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP006Output2559, pairMagnitude2542]

def batchValueN05120MinusP007Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP007Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP007Output2559.1‖ ≤ (batchValueN05120MinusP007Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP007BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP007Output2559,
    batchN05120MinusP007Center2559, batchN05120MinusP007Error2559, embedPair2542]

theorem batchValueN05120MinusP007Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP007Output2559.1) + embedPair2542
            batchValueN05120MinusP007Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP007Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP007Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP007Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP007Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP007Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP007Output2559, pairMagnitude2542]

def batchValueN05120MinusP008Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP008Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP008Output2559.1‖ ≤ (batchValueN05120MinusP008Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP008BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP008Output2559,
    batchN05120MinusP008Center2559, batchN05120MinusP008Error2559, embedPair2542]

theorem batchValueN05120MinusP008Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP008Output2559.1) + embedPair2542
            batchValueN05120MinusP008Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP008Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP008Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP008Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP008Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP008Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP008Output2559, pairMagnitude2542]

def batchValueN05120MinusP009Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP009Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP009Output2559.1‖ ≤ (batchValueN05120MinusP009Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP009BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP009Output2559,
    batchN05120MinusP009Center2559, batchN05120MinusP009Error2559, embedPair2542]

theorem batchValueN05120MinusP009Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP009Output2559.1) + embedPair2542
            batchValueN05120MinusP009Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP009Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP009Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP009Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP009Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP009Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP009Output2559, pairMagnitude2542]

def batchValueN05120MinusP010Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP010Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP010Output2559.1‖ ≤ (batchValueN05120MinusP010Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP010BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP010Output2559,
    batchN05120MinusP010Center2559, batchN05120MinusP010Error2559, embedPair2542]

theorem batchValueN05120MinusP010Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP010Output2559.1) + embedPair2542
            batchValueN05120MinusP010Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP010Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP010Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP010Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP010Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP010Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP010Output2559, pairMagnitude2542]

def batchValueN05120MinusP011Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP011Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP011Output2559.1‖ ≤ (batchValueN05120MinusP011Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP011BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP011Output2559,
    batchN05120MinusP011Center2559, batchN05120MinusP011Error2559, embedPair2542]

theorem batchValueN05120MinusP011Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP011Output2559.1) + embedPair2542
            batchValueN05120MinusP011Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP011Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP011Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP011Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP011Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP011Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP011Output2559, pairMagnitude2542]

def batchValueN05120MinusP012Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP012Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP012Output2559.1‖ ≤ (batchValueN05120MinusP012Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP012BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP012Output2559,
    batchN05120MinusP012Center2559, batchN05120MinusP012Error2559, embedPair2542]

theorem batchValueN05120MinusP012Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP012Output2559.1) + embedPair2542
            batchValueN05120MinusP012Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP012Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP012Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP012Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP012Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP012Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP012Output2559, pairMagnitude2542]

def batchValueN05120MinusP013Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP013Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP013Output2559.1‖ ≤ (batchValueN05120MinusP013Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP013BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP013Output2559,
    batchN05120MinusP013Center2559, batchN05120MinusP013Error2559, embedPair2542]

theorem batchValueN05120MinusP013Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP013Output2559.1) + embedPair2542
            batchValueN05120MinusP013Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP013Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP013Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP013Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP013Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP013Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP013Output2559, pairMagnitude2542]

def batchValueN05120MinusP014Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP014Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP014Output2559.1‖ ≤ (batchValueN05120MinusP014Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP014BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP014Output2559,
    batchN05120MinusP014Center2559, batchN05120MinusP014Error2559, embedPair2542]

theorem batchValueN05120MinusP014Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP014Output2559.1) + embedPair2542
            batchValueN05120MinusP014Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP014Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP014Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP014Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP014Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP014Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP014Output2559, pairMagnitude2542]

def batchValueN05120MinusP015Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP015Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP015Output2559.1‖ ≤ (batchValueN05120MinusP015Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP015BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP015Output2559,
    batchN05120MinusP015Center2559, batchN05120MinusP015Error2559, embedPair2542]

theorem batchValueN05120MinusP015Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP015Output2559.1) + embedPair2542
            batchValueN05120MinusP015Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP015Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP015Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP015Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP015Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP015Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP015Output2559, pairMagnitude2542]

def batchValueN05120MinusP016Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP016Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP016Output2559.1‖ ≤ (batchValueN05120MinusP016Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP016BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP016Output2559,
    batchN05120MinusP016Center2559, batchN05120MinusP016Error2559, embedPair2542]

theorem batchValueN05120MinusP016Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP016Output2559.1) + embedPair2542
            batchValueN05120MinusP016Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP016Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP016Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP016Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP016Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP016Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP016Output2559, pairMagnitude2542]

def batchValueN05120MinusP017Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP017Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP017Output2559.1‖ ≤ (batchValueN05120MinusP017Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP017BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP017Output2559,
    batchN05120MinusP017Center2559, batchN05120MinusP017Error2559, embedPair2542]

theorem batchValueN05120MinusP017Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP017Output2559.1) + embedPair2542
            batchValueN05120MinusP017Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP017Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP017Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP017Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP017Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP017Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP017Output2559, pairMagnitude2542]

def batchValueN05120MinusP018Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP018Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP018Output2559.1‖ ≤ (batchValueN05120MinusP018Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP018BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP018Output2559,
    batchN05120MinusP018Center2559, batchN05120MinusP018Error2559, embedPair2542]

theorem batchValueN05120MinusP018Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP018Output2559.1) + embedPair2542
            batchValueN05120MinusP018Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP018Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP018Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP018Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP018Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP018Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP018Output2559, pairMagnitude2542]

def batchValueN05120MinusP019Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP019Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP019Output2559.1‖ ≤ (batchValueN05120MinusP019Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP019BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP019Output2559,
    batchN05120MinusP019Center2559, batchN05120MinusP019Error2559, embedPair2542]

theorem batchValueN05120MinusP019Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP019Output2559.1) + embedPair2542
            batchValueN05120MinusP019Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP019Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP019Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP019Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP019Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP019Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP019Output2559, pairMagnitude2542]

def batchValueN05120MinusP020Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP020Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP020Output2559.1‖ ≤ (batchValueN05120MinusP020Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP020BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP020Output2559,
    batchN05120MinusP020Center2559, batchN05120MinusP020Error2559, embedPair2542]

theorem batchValueN05120MinusP020Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP020Output2559.1) + embedPair2542
            batchValueN05120MinusP020Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP020Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP020Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP020Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP020Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP020Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP020Output2559, pairMagnitude2542]

def batchValueN05120MinusP021Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP021Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP021Output2559.1‖ ≤ (batchValueN05120MinusP021Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP021BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP021Output2559,
    batchN05120MinusP021Center2559, batchN05120MinusP021Error2559, embedPair2542]

theorem batchValueN05120MinusP021Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP021Output2559.1) + embedPair2542
            batchValueN05120MinusP021Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP021Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP021Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP021Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP021Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP021Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP021Output2559, pairMagnitude2542]

def batchValueN05120MinusP022Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP022Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP022Output2559.1‖ ≤ (batchValueN05120MinusP022Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP022BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP022Output2559,
    batchN05120MinusP022Center2559, batchN05120MinusP022Error2559, embedPair2542]

theorem batchValueN05120MinusP022Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP022Output2559.1) + embedPair2542
            batchValueN05120MinusP022Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP022Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP022Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP022Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP022Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP022Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP022Output2559, pairMagnitude2542]

def batchValueN05120MinusP023Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP023Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP023Output2559.1‖ ≤ (batchValueN05120MinusP023Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP023BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP023Output2559,
    batchN05120MinusP023Center2559, batchN05120MinusP023Error2559, embedPair2542]

theorem batchValueN05120MinusP023Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP023Output2559.1) + embedPair2542
            batchValueN05120MinusP023Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP023Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP023Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP023Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP023Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP023Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP023Output2559, pairMagnitude2542]

def batchValueN05120MinusP024Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP024Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP024Output2559.1‖ ≤ (batchValueN05120MinusP024Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP024BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP024Output2559,
    batchN05120MinusP024Center2559, batchN05120MinusP024Error2559, embedPair2542]

theorem batchValueN05120MinusP024Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP024Output2559.1) + embedPair2542
            batchValueN05120MinusP024Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP024Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP024Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP024Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP024Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP024Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP024Output2559, pairMagnitude2542]

def batchValueN05120MinusP025Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP025Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP025Output2559.1‖ ≤ (batchValueN05120MinusP025Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP025BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP025Output2559,
    batchN05120MinusP025Center2559, batchN05120MinusP025Error2559, embedPair2542]

theorem batchValueN05120MinusP025Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP025Output2559.1) + embedPair2542
            batchValueN05120MinusP025Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP025Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP025Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP025Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP025Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP025Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP025Output2559, pairMagnitude2542]

def batchValueN05120MinusP026Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP026Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP026Output2559.1‖ ≤ (batchValueN05120MinusP026Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP026BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP026Output2559,
    batchN05120MinusP026Center2559, batchN05120MinusP026Error2559, embedPair2542]

theorem batchValueN05120MinusP026Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP026Output2559.1) + embedPair2542
            batchValueN05120MinusP026Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP026Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP026Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP026Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP026Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP026Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP026Output2559, pairMagnitude2542]

def batchValueN05120MinusP027Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP027Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP027Output2559.1‖ ≤ (batchValueN05120MinusP027Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP027BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP027Output2559,
    batchN05120MinusP027Center2559, batchN05120MinusP027Error2559, embedPair2542]

theorem batchValueN05120MinusP027Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP027Output2559.1) + embedPair2542
            batchValueN05120MinusP027Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP027Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP027Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP027Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP027Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP027Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP027Output2559, pairMagnitude2542]

def batchValueN05120MinusP028Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP028Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP028Output2559.1‖ ≤ (batchValueN05120MinusP028Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP028BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP028Output2559,
    batchN05120MinusP028Center2559, batchN05120MinusP028Error2559, embedPair2542]

theorem batchValueN05120MinusP028Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP028Output2559.1) + embedPair2542
            batchValueN05120MinusP028Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP028Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP028Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP028Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP028Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP028Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP028Output2559, pairMagnitude2542]

def batchValueN05120MinusP029Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120MinusP029Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP029Output2559.1‖ ≤ (batchValueN05120MinusP029Output2559.2 : ℝ)
                := by
  have h := batchN05120MinusP029BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120MinusPosition2559, batchN05120MinusPosition2559,
      batchValueN05120MinusP029Output2559,
    batchN05120MinusP029Center2559, batchN05120MinusP029Error2559, embedPair2542]

theorem batchValueN05120MinusP029Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05120MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05120MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP029Output2559.1) + embedPair2542
            batchValueN05120MinusP029Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05120MinusPosition2559 - embedPair2542
            batchValueN05120MinusP029Output2559.1‖ + ‖embedPair2542
            batchValueN05120MinusP029Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120MinusP029Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120MinusP029Output2559.1 : ℝ) :=
      add_le_add batchValueN05120MinusP029Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120MinusP029Output2559, pairMagnitude2542]

noncomputable def batchValueN05120MinusValue2559 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchValueN05120MinusP000Output2559.1
  | 1 => embedPair2542 batchValueN05120MinusP001Output2559.1
  | 2 => embedPair2542 batchValueN05120MinusP002Output2559.1
  | 3 => embedPair2542 batchValueN05120MinusP003Output2559.1
  | 4 => embedPair2542 batchValueN05120MinusP004Output2559.1
  | 5 => embedPair2542 batchValueN05120MinusP005Output2559.1
  | 6 => embedPair2542 batchValueN05120MinusP006Output2559.1
  | 7 => embedPair2542 batchValueN05120MinusP007Output2559.1
  | 8 => embedPair2542 batchValueN05120MinusP008Output2559.1
  | 9 => embedPair2542 batchValueN05120MinusP009Output2559.1
  | 10 => embedPair2542 batchValueN05120MinusP010Output2559.1
  | 11 => embedPair2542 batchValueN05120MinusP011Output2559.1
  | 12 => embedPair2542 batchValueN05120MinusP012Output2559.1
  | 13 => embedPair2542 batchValueN05120MinusP013Output2559.1
  | 14 => embedPair2542 batchValueN05120MinusP014Output2559.1
  | 15 => embedPair2542 batchValueN05120MinusP015Output2559.1
  | 16 => embedPair2542 batchValueN05120MinusP016Output2559.1
  | 17 => embedPair2542 batchValueN05120MinusP017Output2559.1
  | 18 => embedPair2542 batchValueN05120MinusP018Output2559.1
  | 19 => embedPair2542 batchValueN05120MinusP019Output2559.1
  | 20 => embedPair2542 batchValueN05120MinusP020Output2559.1
  | 21 => embedPair2542 batchValueN05120MinusP021Output2559.1
  | 22 => embedPair2542 batchValueN05120MinusP022Output2559.1
  | 23 => embedPair2542 batchValueN05120MinusP023Output2559.1
  | 24 => embedPair2542 batchValueN05120MinusP024Output2559.1
  | 25 => embedPair2542 batchValueN05120MinusP025Output2559.1
  | 26 => embedPair2542 batchValueN05120MinusP026Output2559.1
  | 27 => embedPair2542 batchValueN05120MinusP027Output2559.1
  | 28 => embedPair2542 batchValueN05120MinusP028Output2559.1
  | 29 => embedPair2542 batchValueN05120MinusP029Output2559.1
  | _ => 0

noncomputable def batchValueN05120MinusError2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (batchValueN05120MinusP000Output2559.2 : ℝ)
  | 1 => (batchValueN05120MinusP001Output2559.2 : ℝ)
  | 2 => (batchValueN05120MinusP002Output2559.2 : ℝ)
  | 3 => (batchValueN05120MinusP003Output2559.2 : ℝ)
  | 4 => (batchValueN05120MinusP004Output2559.2 : ℝ)
  | 5 => (batchValueN05120MinusP005Output2559.2 : ℝ)
  | 6 => (batchValueN05120MinusP006Output2559.2 : ℝ)
  | 7 => (batchValueN05120MinusP007Output2559.2 : ℝ)
  | 8 => (batchValueN05120MinusP008Output2559.2 : ℝ)
  | 9 => (batchValueN05120MinusP009Output2559.2 : ℝ)
  | 10 => (batchValueN05120MinusP010Output2559.2 : ℝ)
  | 11 => (batchValueN05120MinusP011Output2559.2 : ℝ)
  | 12 => (batchValueN05120MinusP012Output2559.2 : ℝ)
  | 13 => (batchValueN05120MinusP013Output2559.2 : ℝ)
  | 14 => (batchValueN05120MinusP014Output2559.2 : ℝ)
  | 15 => (batchValueN05120MinusP015Output2559.2 : ℝ)
  | 16 => (batchValueN05120MinusP016Output2559.2 : ℝ)
  | 17 => (batchValueN05120MinusP017Output2559.2 : ℝ)
  | 18 => (batchValueN05120MinusP018Output2559.2 : ℝ)
  | 19 => (batchValueN05120MinusP019Output2559.2 : ℝ)
  | 20 => (batchValueN05120MinusP020Output2559.2 : ℝ)
  | 21 => (batchValueN05120MinusP021Output2559.2 : ℝ)
  | 22 => (batchValueN05120MinusP022Output2559.2 : ℝ)
  | 23 => (batchValueN05120MinusP023Output2559.2 : ℝ)
  | 24 => (batchValueN05120MinusP024Output2559.2 : ℝ)
  | 25 => (batchValueN05120MinusP025Output2559.2 : ℝ)
  | 26 => (batchValueN05120MinusP026Output2559.2 : ℝ)
  | 27 => (batchValueN05120MinusP027Output2559.2 : ℝ)
  | 28 => (batchValueN05120MinusP028Output2559.2 : ℝ)
  | 29 => (batchValueN05120MinusP029Output2559.2 : ℝ)
  | _ => 0

theorem batchValueN05120MinusExp_error2559 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05120MinusPosition2559 -
            batchValueN05120MinusValue2559 i‖
            ≤ batchValueN05120MinusError2559 i := by
  fin_cases i
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP000Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP001Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP002Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP003Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP004Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP005Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP006Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP007Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP008Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP009Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP010Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP011Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP012Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP013Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP014Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP015Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP016Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP017Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP018Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP019Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP020Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP021Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP022Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP023Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP024Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP025Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP026Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP027Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP028Error2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP029Error2559

theorem batchValueN05120MinusUnit_norm2559 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05120MinusPosition2559‖ ≤ 1 := by
  fin_cases i
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP000Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP001Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP002Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP003Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP004Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP005Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP006Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP007Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP008Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP009Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP010Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP011Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP012Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP013Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP014Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP015Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP016Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP017Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP018Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP019Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP020Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP021Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP022Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP023Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP024Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP025Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP026Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP027Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP028Norm2559
  · simpa only [batchValueN05120MinusValue2559, batchValueN05120MinusError2559] using
      batchValueN05120MinusP029Norm2559

noncomputable def batchValueN05120MinusSumValue2559 : ℂ := ⟨(((((2506798687244798 * 10^40
        + 8180631581266596923616791573534563413771) * 10^40
        + 6486797105857378996885527329640832345948) * 10^40
        + 8487226150265871929866184782539526991225) : ℝ) /
        (((181709681073901 * 10^40
        + 7226373309519720011335884103401718295150) * 10^40
        + 7037254979515982202834948083154776267844) * 10^40
        + 891390190630401566544483383650407153664)),
    (((((88040834782652373986136 * 10^40
        + 1440507889421642294640659365856774768125) * 10^40
        + 4669435078406585992033047026747000745992) * 10^40
        + 2287797425386562640864265015080005787555) : ℝ) /
        (((49947976805055875702105555 * 10^40
        + 6766906608919775702826395384137465113540) * 10^40
        + 594782111624992192489764901587153855723) * 10^40
        + 897942505966327167610868612564900642816))⟩

noncomputable def batchValueN05120MinusUpper2559 : ℝ := ((27591250977 : ℝ) /
        2000000000)

theorem batchValueN05120MinusSum_eq2559 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05120MinusValue2559 i) =
      batchValueN05120MinusSumValue2559 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN05120MinusValue2559,
      batchValueN05120MinusSumValue2559, embedPair2542, batchValueN05120MinusP000Output2559,
      batchValueN05120MinusP001Output2559,
      batchValueN05120MinusP002Output2559,
      batchValueN05120MinusP003Output2559,
      batchValueN05120MinusP004Output2559,
      batchValueN05120MinusP005Output2559,
      batchValueN05120MinusP006Output2559,
      batchValueN05120MinusP007Output2559,
      batchValueN05120MinusP008Output2559,
      batchValueN05120MinusP009Output2559,
      batchValueN05120MinusP010Output2559,
      batchValueN05120MinusP011Output2559,
      batchValueN05120MinusP012Output2559,
      batchValueN05120MinusP013Output2559,
      batchValueN05120MinusP014Output2559,
      batchValueN05120MinusP015Output2559,
      batchValueN05120MinusP016Output2559,
      batchValueN05120MinusP017Output2559,
      batchValueN05120MinusP018Output2559,
      batchValueN05120MinusP019Output2559,
      batchValueN05120MinusP020Output2559,
      batchValueN05120MinusP021Output2559,
      batchValueN05120MinusP022Output2559,
      batchValueN05120MinusP023Output2559,
      batchValueN05120MinusP024Output2559,
      batchValueN05120MinusP025Output2559,
      batchValueN05120MinusP026Output2559,
      batchValueN05120MinusP027Output2559,
      batchValueN05120MinusP028Output2559,
      batchValueN05120MinusP029Output2559, Complex.mul_re, Complex.mul_im]

theorem batchValueN05120MinusSum_norm2559 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05120MinusValue2559 i‖ ≤
      ((34489063721 : ℝ) /
        2500000000) := by
  rw [batchValueN05120MinusSum_eq2559]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchValueN05120MinusSumValue2559]

theorem batchValueN05120MinusEvaluation_charge2559 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchValueN05120MinusError2559 i) ≤ (1 : ℝ)/10^12 :=
          by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN05120MinusError2559,
      batchValueN05120MinusP000Output2559,
      batchValueN05120MinusP001Output2559,
      batchValueN05120MinusP002Output2559,
      batchValueN05120MinusP003Output2559,
      batchValueN05120MinusP004Output2559,
      batchValueN05120MinusP005Output2559,
      batchValueN05120MinusP006Output2559,
      batchValueN05120MinusP007Output2559,
      batchValueN05120MinusP008Output2559,
      batchValueN05120MinusP009Output2559,
      batchValueN05120MinusP010Output2559,
      batchValueN05120MinusP011Output2559,
      batchValueN05120MinusP012Output2559,
      batchValueN05120MinusP013Output2559,
      batchValueN05120MinusP014Output2559,
      batchValueN05120MinusP015Output2559,
      batchValueN05120MinusP016Output2559,
      batchValueN05120MinusP017Output2559,
      batchValueN05120MinusP018Output2559,
      batchValueN05120MinusP019Output2559,
      batchValueN05120MinusP020Output2559,
      batchValueN05120MinusP021Output2559,
      batchValueN05120MinusP022Output2559,
      batchValueN05120MinusP023Output2559,
      batchValueN05120MinusP024Output2559,
      batchValueN05120MinusP025Output2559,
      batchValueN05120MinusP026Output2559,
      batchValueN05120MinusP027Output2559,
      batchValueN05120MinusP028Output2559,
      batchValueN05120MinusP029Output2559]

theorem batchValueN05120MinusSigned_le2559 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchValueN05120MinusPosition2559 ≤ batchValueN05120MinusUpper2559 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05120MinusPosition2559‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05120MinusValue2559 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchValueN05120MinusError2559 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (batchValueN05120MinusExp_error2559 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05120MinusPosition2559‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchValueN05120MinusUnit_norm2559 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05120MinusPosition2559‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchValueN05120MinusUpper2559
  linarith [batchValueN05120MinusSum_norm2559, batchValueN05120MinusEvaluation_charge2559]

theorem batchValueN05120MinusPhysical_le2559 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 batchValueN05120MinusPosition2559‖ ≤
      batchValueN05120MinusUpper2559 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchValueN05120MinusPosition2559
  simpa only [iteratedDeriv_zero] using h.trans batchValueN05120MinusSigned_le2559

theorem batchValueN05120MinusGrid2559 :
    -stripRadius2303 + (5120 : ℝ)*(2*stripRadius2303/10240) = batchValueN05120MinusPosition2559 :=
        by
  norm_num [stripRadius2303, batchValueN05120MinusPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchValueN05120MinusSigned_le2559
#print axioms ConnesWeilRH.Dev.batchValueN05120MinusPhysical_le2559
