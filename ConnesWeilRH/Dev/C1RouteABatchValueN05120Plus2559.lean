import ConnesWeilRH.Dev.C1RouteABatchN05120Plus2559
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchValueN05120PlusPosition2559 : ℝ := (0 : ℝ)

def batchValueN05120PlusP000Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP000Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP000Output2559.1‖ ≤ (batchValueN05120PlusP000Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP000BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP000Output2559,
    batchN05120PlusP000Center2559, batchN05120PlusP000Error2559, embedPair2542]

theorem batchValueN05120PlusP000Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP000Output2559.1) + embedPair2542
            batchValueN05120PlusP000Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP000Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP000Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP000Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP000Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP000Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP000Output2559, pairMagnitude2542]

def batchValueN05120PlusP001Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP001Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP001Output2559.1‖ ≤ (batchValueN05120PlusP001Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP001BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP001Output2559,
    batchN05120PlusP001Center2559, batchN05120PlusP001Error2559, embedPair2542]

theorem batchValueN05120PlusP001Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP001Output2559.1) + embedPair2542
            batchValueN05120PlusP001Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP001Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP001Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP001Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP001Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP001Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP001Output2559, pairMagnitude2542]

def batchValueN05120PlusP002Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP002Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP002Output2559.1‖ ≤ (batchValueN05120PlusP002Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP002BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP002Output2559,
    batchN05120PlusP002Center2559, batchN05120PlusP002Error2559, embedPair2542]

theorem batchValueN05120PlusP002Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP002Output2559.1) + embedPair2542
            batchValueN05120PlusP002Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP002Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP002Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP002Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP002Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP002Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP002Output2559, pairMagnitude2542]

def batchValueN05120PlusP003Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP003Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP003Output2559.1‖ ≤ (batchValueN05120PlusP003Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP003BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP003Output2559,
    batchN05120PlusP003Center2559, batchN05120PlusP003Error2559, embedPair2542]

theorem batchValueN05120PlusP003Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP003Output2559.1) + embedPair2542
            batchValueN05120PlusP003Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP003Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP003Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP003Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP003Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP003Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP003Output2559, pairMagnitude2542]

def batchValueN05120PlusP004Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP004Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP004Output2559.1‖ ≤ (batchValueN05120PlusP004Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP004BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP004Output2559,
    batchN05120PlusP004Center2559, batchN05120PlusP004Error2559, embedPair2542]

theorem batchValueN05120PlusP004Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP004Output2559.1) + embedPair2542
            batchValueN05120PlusP004Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP004Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP004Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP004Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP004Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP004Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP004Output2559, pairMagnitude2542]

def batchValueN05120PlusP005Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP005Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP005Output2559.1‖ ≤ (batchValueN05120PlusP005Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP005BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP005Output2559,
    batchN05120PlusP005Center2559, batchN05120PlusP005Error2559, embedPair2542]

theorem batchValueN05120PlusP005Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP005Output2559.1) + embedPair2542
            batchValueN05120PlusP005Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP005Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP005Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP005Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP005Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP005Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP005Output2559, pairMagnitude2542]

def batchValueN05120PlusP006Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP006Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP006Output2559.1‖ ≤ (batchValueN05120PlusP006Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP006BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP006Output2559,
    batchN05120PlusP006Center2559, batchN05120PlusP006Error2559, embedPair2542]

theorem batchValueN05120PlusP006Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP006Output2559.1) + embedPair2542
            batchValueN05120PlusP006Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP006Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP006Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP006Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP006Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP006Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP006Output2559, pairMagnitude2542]

def batchValueN05120PlusP007Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP007Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP007Output2559.1‖ ≤ (batchValueN05120PlusP007Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP007BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP007Output2559,
    batchN05120PlusP007Center2559, batchN05120PlusP007Error2559, embedPair2542]

theorem batchValueN05120PlusP007Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP007Output2559.1) + embedPair2542
            batchValueN05120PlusP007Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP007Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP007Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP007Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP007Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP007Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP007Output2559, pairMagnitude2542]

def batchValueN05120PlusP008Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP008Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP008Output2559.1‖ ≤ (batchValueN05120PlusP008Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP008BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP008Output2559,
    batchN05120PlusP008Center2559, batchN05120PlusP008Error2559, embedPair2542]

theorem batchValueN05120PlusP008Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP008Output2559.1) + embedPair2542
            batchValueN05120PlusP008Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP008Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP008Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP008Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP008Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP008Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP008Output2559, pairMagnitude2542]

def batchValueN05120PlusP009Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP009Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP009Output2559.1‖ ≤ (batchValueN05120PlusP009Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP009BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP009Output2559,
    batchN05120PlusP009Center2559, batchN05120PlusP009Error2559, embedPair2542]

theorem batchValueN05120PlusP009Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP009Output2559.1) + embedPair2542
            batchValueN05120PlusP009Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP009Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP009Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP009Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP009Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP009Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP009Output2559, pairMagnitude2542]

def batchValueN05120PlusP010Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP010Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP010Output2559.1‖ ≤ (batchValueN05120PlusP010Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP010BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP010Output2559,
    batchN05120PlusP010Center2559, batchN05120PlusP010Error2559, embedPair2542]

theorem batchValueN05120PlusP010Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP010Output2559.1) + embedPair2542
            batchValueN05120PlusP010Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP010Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP010Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP010Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP010Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP010Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP010Output2559, pairMagnitude2542]

def batchValueN05120PlusP011Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP011Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP011Output2559.1‖ ≤ (batchValueN05120PlusP011Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP011BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP011Output2559,
    batchN05120PlusP011Center2559, batchN05120PlusP011Error2559, embedPair2542]

theorem batchValueN05120PlusP011Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP011Output2559.1) + embedPair2542
            batchValueN05120PlusP011Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP011Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP011Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP011Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP011Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP011Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP011Output2559, pairMagnitude2542]

def batchValueN05120PlusP012Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP012Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP012Output2559.1‖ ≤ (batchValueN05120PlusP012Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP012BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP012Output2559,
    batchN05120PlusP012Center2559, batchN05120PlusP012Error2559, embedPair2542]

theorem batchValueN05120PlusP012Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP012Output2559.1) + embedPair2542
            batchValueN05120PlusP012Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP012Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP012Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP012Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP012Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP012Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP012Output2559, pairMagnitude2542]

def batchValueN05120PlusP013Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP013Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP013Output2559.1‖ ≤ (batchValueN05120PlusP013Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP013BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP013Output2559,
    batchN05120PlusP013Center2559, batchN05120PlusP013Error2559, embedPair2542]

theorem batchValueN05120PlusP013Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP013Output2559.1) + embedPair2542
            batchValueN05120PlusP013Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP013Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP013Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP013Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP013Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP013Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP013Output2559, pairMagnitude2542]

def batchValueN05120PlusP014Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP014Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP014Output2559.1‖ ≤ (batchValueN05120PlusP014Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP014BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP014Output2559,
    batchN05120PlusP014Center2559, batchN05120PlusP014Error2559, embedPair2542]

theorem batchValueN05120PlusP014Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP014Output2559.1) + embedPair2542
            batchValueN05120PlusP014Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP014Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP014Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP014Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP014Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP014Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP014Output2559, pairMagnitude2542]

def batchValueN05120PlusP015Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP015Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP015Output2559.1‖ ≤ (batchValueN05120PlusP015Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP015BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP015Output2559,
    batchN05120PlusP015Center2559, batchN05120PlusP015Error2559, embedPair2542]

theorem batchValueN05120PlusP015Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP015Output2559.1) + embedPair2542
            batchValueN05120PlusP015Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP015Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP015Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP015Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP015Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP015Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP015Output2559, pairMagnitude2542]

def batchValueN05120PlusP016Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP016Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP016Output2559.1‖ ≤ (batchValueN05120PlusP016Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP016BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP016Output2559,
    batchN05120PlusP016Center2559, batchN05120PlusP016Error2559, embedPair2542]

theorem batchValueN05120PlusP016Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP016Output2559.1) + embedPair2542
            batchValueN05120PlusP016Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP016Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP016Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP016Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP016Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP016Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP016Output2559, pairMagnitude2542]

def batchValueN05120PlusP017Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP017Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP017Output2559.1‖ ≤ (batchValueN05120PlusP017Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP017BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP017Output2559,
    batchN05120PlusP017Center2559, batchN05120PlusP017Error2559, embedPair2542]

theorem batchValueN05120PlusP017Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP017Output2559.1) + embedPair2542
            batchValueN05120PlusP017Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP017Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP017Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP017Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP017Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP017Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP017Output2559, pairMagnitude2542]

def batchValueN05120PlusP018Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP018Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP018Output2559.1‖ ≤ (batchValueN05120PlusP018Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP018BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP018Output2559,
    batchN05120PlusP018Center2559, batchN05120PlusP018Error2559, embedPair2542]

theorem batchValueN05120PlusP018Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP018Output2559.1) + embedPair2542
            batchValueN05120PlusP018Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP018Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP018Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP018Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP018Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP018Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP018Output2559, pairMagnitude2542]

def batchValueN05120PlusP019Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP019Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP019Output2559.1‖ ≤ (batchValueN05120PlusP019Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP019BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP019Output2559,
    batchN05120PlusP019Center2559, batchN05120PlusP019Error2559, embedPair2542]

theorem batchValueN05120PlusP019Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP019Output2559.1) + embedPair2542
            batchValueN05120PlusP019Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP019Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP019Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP019Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP019Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP019Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP019Output2559, pairMagnitude2542]

def batchValueN05120PlusP020Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP020Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP020Output2559.1‖ ≤ (batchValueN05120PlusP020Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP020BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP020Output2559,
    batchN05120PlusP020Center2559, batchN05120PlusP020Error2559, embedPair2542]

theorem batchValueN05120PlusP020Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP020Output2559.1) + embedPair2542
            batchValueN05120PlusP020Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP020Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP020Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP020Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP020Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP020Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP020Output2559, pairMagnitude2542]

def batchValueN05120PlusP021Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP021Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP021Output2559.1‖ ≤ (batchValueN05120PlusP021Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP021BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP021Output2559,
    batchN05120PlusP021Center2559, batchN05120PlusP021Error2559, embedPair2542]

theorem batchValueN05120PlusP021Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP021Output2559.1) + embedPair2542
            batchValueN05120PlusP021Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP021Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP021Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP021Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP021Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP021Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP021Output2559, pairMagnitude2542]

def batchValueN05120PlusP022Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP022Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP022Output2559.1‖ ≤ (batchValueN05120PlusP022Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP022BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP022Output2559,
    batchN05120PlusP022Center2559, batchN05120PlusP022Error2559, embedPair2542]

theorem batchValueN05120PlusP022Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP022Output2559.1) + embedPair2542
            batchValueN05120PlusP022Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP022Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP022Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP022Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP022Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP022Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP022Output2559, pairMagnitude2542]

def batchValueN05120PlusP023Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP023Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP023Output2559.1‖ ≤ (batchValueN05120PlusP023Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP023BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP023Output2559,
    batchN05120PlusP023Center2559, batchN05120PlusP023Error2559, embedPair2542]

theorem batchValueN05120PlusP023Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP023Output2559.1) + embedPair2542
            batchValueN05120PlusP023Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP023Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP023Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP023Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP023Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP023Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP023Output2559, pairMagnitude2542]

def batchValueN05120PlusP024Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP024Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP024Output2559.1‖ ≤ (batchValueN05120PlusP024Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP024BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP024Output2559,
    batchN05120PlusP024Center2559, batchN05120PlusP024Error2559, embedPair2542]

theorem batchValueN05120PlusP024Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP024Output2559.1) + embedPair2542
            batchValueN05120PlusP024Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP024Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP024Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP024Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP024Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP024Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP024Output2559, pairMagnitude2542]

def batchValueN05120PlusP025Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP025Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP025Output2559.1‖ ≤ (batchValueN05120PlusP025Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP025BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP025Output2559,
    batchN05120PlusP025Center2559, batchN05120PlusP025Error2559, embedPair2542]

theorem batchValueN05120PlusP025Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP025Output2559.1) + embedPair2542
            batchValueN05120PlusP025Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP025Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP025Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP025Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP025Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP025Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP025Output2559, pairMagnitude2542]

def batchValueN05120PlusP026Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP026Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP026Output2559.1‖ ≤ (batchValueN05120PlusP026Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP026BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP026Output2559,
    batchN05120PlusP026Center2559, batchN05120PlusP026Error2559, embedPair2542]

theorem batchValueN05120PlusP026Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP026Output2559.1) + embedPair2542
            batchValueN05120PlusP026Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP026Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP026Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP026Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP026Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP026Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP026Output2559, pairMagnitude2542]

def batchValueN05120PlusP027Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP027Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP027Output2559.1‖ ≤ (batchValueN05120PlusP027Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP027BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP027Output2559,
    batchN05120PlusP027Center2559, batchN05120PlusP027Error2559, embedPair2542]

theorem batchValueN05120PlusP027Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP027Output2559.1) + embedPair2542
            batchValueN05120PlusP027Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP027Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP027Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP027Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP027Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP027Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP027Output2559, pairMagnitude2542]

def batchValueN05120PlusP028Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP028Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP028Output2559.1‖ ≤ (batchValueN05120PlusP028Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP028BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP028Output2559,
    batchN05120PlusP028Center2559, batchN05120PlusP028Error2559, embedPair2542]

theorem batchValueN05120PlusP028Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP028Output2559.1) + embedPair2542
            batchValueN05120PlusP028Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP028Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP028Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP028Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP028Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP028Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP028Output2559, pairMagnitude2542]

def batchValueN05120PlusP029Output2559 : RatState2542 :=
  ((((136761812904851798033513937177447845 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1)),
    ((12287562243733755928524809515635 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05120PlusP029Error2559 :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP029Output2559.1‖ ≤ (batchValueN05120PlusP029Output2559.2 : ℝ) :=
                by
  have h := batchN05120PlusP029BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05120PlusPosition2559, batchN05120PlusPosition2559,
      batchValueN05120PlusP029Output2559,
    batchN05120PlusP029Center2559, batchN05120PlusP029Error2559, embedPair2542]

theorem batchValueN05120PlusP029Norm2559 : ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05120PlusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05120PlusPosition2559‖ =
            ‖(weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP029Output2559.1) + embedPair2542
            batchValueN05120PlusP029Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05120PlusPosition2559 - embedPair2542
            batchValueN05120PlusP029Output2559.1‖ + ‖embedPair2542
            batchValueN05120PlusP029Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05120PlusP029Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05120PlusP029Output2559.1 : ℝ) :=
      add_le_add batchValueN05120PlusP029Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05120PlusP029Output2559, pairMagnitude2542]

noncomputable def batchValueN05120PlusValue2559 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchValueN05120PlusP000Output2559.1
  | 1 => embedPair2542 batchValueN05120PlusP001Output2559.1
  | 2 => embedPair2542 batchValueN05120PlusP002Output2559.1
  | 3 => embedPair2542 batchValueN05120PlusP003Output2559.1
  | 4 => embedPair2542 batchValueN05120PlusP004Output2559.1
  | 5 => embedPair2542 batchValueN05120PlusP005Output2559.1
  | 6 => embedPair2542 batchValueN05120PlusP006Output2559.1
  | 7 => embedPair2542 batchValueN05120PlusP007Output2559.1
  | 8 => embedPair2542 batchValueN05120PlusP008Output2559.1
  | 9 => embedPair2542 batchValueN05120PlusP009Output2559.1
  | 10 => embedPair2542 batchValueN05120PlusP010Output2559.1
  | 11 => embedPair2542 batchValueN05120PlusP011Output2559.1
  | 12 => embedPair2542 batchValueN05120PlusP012Output2559.1
  | 13 => embedPair2542 batchValueN05120PlusP013Output2559.1
  | 14 => embedPair2542 batchValueN05120PlusP014Output2559.1
  | 15 => embedPair2542 batchValueN05120PlusP015Output2559.1
  | 16 => embedPair2542 batchValueN05120PlusP016Output2559.1
  | 17 => embedPair2542 batchValueN05120PlusP017Output2559.1
  | 18 => embedPair2542 batchValueN05120PlusP018Output2559.1
  | 19 => embedPair2542 batchValueN05120PlusP019Output2559.1
  | 20 => embedPair2542 batchValueN05120PlusP020Output2559.1
  | 21 => embedPair2542 batchValueN05120PlusP021Output2559.1
  | 22 => embedPair2542 batchValueN05120PlusP022Output2559.1
  | 23 => embedPair2542 batchValueN05120PlusP023Output2559.1
  | 24 => embedPair2542 batchValueN05120PlusP024Output2559.1
  | 25 => embedPair2542 batchValueN05120PlusP025Output2559.1
  | 26 => embedPair2542 batchValueN05120PlusP026Output2559.1
  | 27 => embedPair2542 batchValueN05120PlusP027Output2559.1
  | 28 => embedPair2542 batchValueN05120PlusP028Output2559.1
  | 29 => embedPair2542 batchValueN05120PlusP029Output2559.1
  | _ => 0

noncomputable def batchValueN05120PlusError2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (batchValueN05120PlusP000Output2559.2 : ℝ)
  | 1 => (batchValueN05120PlusP001Output2559.2 : ℝ)
  | 2 => (batchValueN05120PlusP002Output2559.2 : ℝ)
  | 3 => (batchValueN05120PlusP003Output2559.2 : ℝ)
  | 4 => (batchValueN05120PlusP004Output2559.2 : ℝ)
  | 5 => (batchValueN05120PlusP005Output2559.2 : ℝ)
  | 6 => (batchValueN05120PlusP006Output2559.2 : ℝ)
  | 7 => (batchValueN05120PlusP007Output2559.2 : ℝ)
  | 8 => (batchValueN05120PlusP008Output2559.2 : ℝ)
  | 9 => (batchValueN05120PlusP009Output2559.2 : ℝ)
  | 10 => (batchValueN05120PlusP010Output2559.2 : ℝ)
  | 11 => (batchValueN05120PlusP011Output2559.2 : ℝ)
  | 12 => (batchValueN05120PlusP012Output2559.2 : ℝ)
  | 13 => (batchValueN05120PlusP013Output2559.2 : ℝ)
  | 14 => (batchValueN05120PlusP014Output2559.2 : ℝ)
  | 15 => (batchValueN05120PlusP015Output2559.2 : ℝ)
  | 16 => (batchValueN05120PlusP016Output2559.2 : ℝ)
  | 17 => (batchValueN05120PlusP017Output2559.2 : ℝ)
  | 18 => (batchValueN05120PlusP018Output2559.2 : ℝ)
  | 19 => (batchValueN05120PlusP019Output2559.2 : ℝ)
  | 20 => (batchValueN05120PlusP020Output2559.2 : ℝ)
  | 21 => (batchValueN05120PlusP021Output2559.2 : ℝ)
  | 22 => (batchValueN05120PlusP022Output2559.2 : ℝ)
  | 23 => (batchValueN05120PlusP023Output2559.2 : ℝ)
  | 24 => (batchValueN05120PlusP024Output2559.2 : ℝ)
  | 25 => (batchValueN05120PlusP025Output2559.2 : ℝ)
  | 26 => (batchValueN05120PlusP026Output2559.2 : ℝ)
  | 27 => (batchValueN05120PlusP027Output2559.2 : ℝ)
  | 28 => (batchValueN05120PlusP028Output2559.2 : ℝ)
  | 29 => (batchValueN05120PlusP029Output2559.2 : ℝ)
  | _ => 0

theorem batchValueN05120PlusExp_error2559 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05120PlusPosition2559 - batchValueN05120PlusValue2559
            i‖ ≤
            batchValueN05120PlusError2559 i := by
  fin_cases i
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP000Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP001Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP002Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP003Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP004Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP005Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP006Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP007Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP008Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP009Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP010Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP011Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP012Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP013Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP014Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP015Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP016Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP017Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP018Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP019Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP020Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP021Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP022Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP023Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP024Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP025Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP026Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP027Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP028Error2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP029Error2559

theorem batchValueN05120PlusUnit_norm2559 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05120PlusPosition2559‖ ≤ 1 := by
  fin_cases i
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP000Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP001Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP002Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP003Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP004Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP005Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP006Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP007Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP008Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP009Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP010Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP011Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP012Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP013Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP014Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP015Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP016Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP017Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP018Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP019Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP020Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP021Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP022Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP023Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP024Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP025Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP026Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP027Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP028Norm2559
  · simpa only [batchValueN05120PlusValue2559, batchValueN05120PlusError2559] using
      batchValueN05120PlusP029Norm2559

noncomputable def batchValueN05120PlusSumValue2559 : ℂ := ⟨(((((2506798687244798 * 10^40
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

noncomputable def batchValueN05120PlusUpper2559 : ℝ := ((27591250977 : ℝ) /
        2000000000)

theorem batchValueN05120PlusSum_eq2559 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05120PlusValue2559 i) =
      batchValueN05120PlusSumValue2559 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN05120PlusValue2559,
      batchValueN05120PlusSumValue2559, embedPair2542, batchValueN05120PlusP000Output2559,
      batchValueN05120PlusP001Output2559,
      batchValueN05120PlusP002Output2559,
      batchValueN05120PlusP003Output2559,
      batchValueN05120PlusP004Output2559,
      batchValueN05120PlusP005Output2559,
      batchValueN05120PlusP006Output2559,
      batchValueN05120PlusP007Output2559,
      batchValueN05120PlusP008Output2559,
      batchValueN05120PlusP009Output2559,
      batchValueN05120PlusP010Output2559,
      batchValueN05120PlusP011Output2559,
      batchValueN05120PlusP012Output2559,
      batchValueN05120PlusP013Output2559,
      batchValueN05120PlusP014Output2559,
      batchValueN05120PlusP015Output2559,
      batchValueN05120PlusP016Output2559,
      batchValueN05120PlusP017Output2559,
      batchValueN05120PlusP018Output2559,
      batchValueN05120PlusP019Output2559,
      batchValueN05120PlusP020Output2559,
      batchValueN05120PlusP021Output2559,
      batchValueN05120PlusP022Output2559,
      batchValueN05120PlusP023Output2559,
      batchValueN05120PlusP024Output2559,
      batchValueN05120PlusP025Output2559,
      batchValueN05120PlusP026Output2559,
      batchValueN05120PlusP027Output2559,
      batchValueN05120PlusP028Output2559,
      batchValueN05120PlusP029Output2559, Complex.mul_re, Complex.mul_im]

theorem batchValueN05120PlusSum_norm2559 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05120PlusValue2559 i‖ ≤
      ((34489063721 : ℝ) /
        2500000000) := by
  rw [batchValueN05120PlusSum_eq2559]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchValueN05120PlusSumValue2559]

theorem batchValueN05120PlusEvaluation_charge2559 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchValueN05120PlusError2559 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN05120PlusError2559,
      batchValueN05120PlusP000Output2559,
      batchValueN05120PlusP001Output2559,
      batchValueN05120PlusP002Output2559,
      batchValueN05120PlusP003Output2559,
      batchValueN05120PlusP004Output2559,
      batchValueN05120PlusP005Output2559,
      batchValueN05120PlusP006Output2559,
      batchValueN05120PlusP007Output2559,
      batchValueN05120PlusP008Output2559,
      batchValueN05120PlusP009Output2559,
      batchValueN05120PlusP010Output2559,
      batchValueN05120PlusP011Output2559,
      batchValueN05120PlusP012Output2559,
      batchValueN05120PlusP013Output2559,
      batchValueN05120PlusP014Output2559,
      batchValueN05120PlusP015Output2559,
      batchValueN05120PlusP016Output2559,
      batchValueN05120PlusP017Output2559,
      batchValueN05120PlusP018Output2559,
      batchValueN05120PlusP019Output2559,
      batchValueN05120PlusP020Output2559,
      batchValueN05120PlusP021Output2559,
      batchValueN05120PlusP022Output2559,
      batchValueN05120PlusP023Output2559,
      batchValueN05120PlusP024Output2559,
      batchValueN05120PlusP025Output2559,
      batchValueN05120PlusP026Output2559,
      batchValueN05120PlusP027Output2559,
      batchValueN05120PlusP028Output2559,
      batchValueN05120PlusP029Output2559]

theorem batchValueN05120PlusSigned_le2559 :
    signedJetUpper2539 0 (((1 : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchValueN05120PlusPosition2559 ≤ batchValueN05120PlusUpper2559 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05120PlusPosition2559‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05120PlusValue2559 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchValueN05120PlusError2559 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (batchValueN05120PlusExp_error2559 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05120PlusPosition2559‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchValueN05120PlusUnit_norm2559 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (((1 : ℝ) /
        2)) nodeModulation2541 i batchValueN05120PlusPosition2559‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchValueN05120PlusUpper2559
  linarith [batchValueN05120PlusSum_norm2559, batchValueN05120PlusEvaluation_charge2559]

theorem batchValueN05120PlusPhysical_le2559 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (((1 : ℝ) /
        2)) coefficients nodeModulation2541 batchValueN05120PlusPosition2559‖ ≤
      batchValueN05120PlusUpper2559 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (((1 : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchValueN05120PlusPosition2559
  simpa only [iteratedDeriv_zero] using h.trans batchValueN05120PlusSigned_le2559

theorem batchValueN05120PlusGrid2559 :
    -stripRadius2303 + (5120 : ℝ)*(2*stripRadius2303/10240) = batchValueN05120PlusPosition2559 :=
        by
  norm_num [stripRadius2303, batchValueN05120PlusPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchValueN05120PlusSigned_le2559
#print axioms ConnesWeilRH.Dev.batchValueN05120PlusPhysical_le2559
