import ConnesWeilRH.Dev.C1RouteABatchN05119Minus2559
import ConnesWeilRH.Dev.C1RouteACompactExp2542
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchValueN05119MinusPosition2559 : ℝ := (((-65536001) : ℝ) /
        51200000000)

def batchValueN05119MinusP000Output2559 : RatState2542 :=
  ((((136675650344030269252347073071421939 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((859099660751348423613761077509565 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872))),
    ((6448820903775322072938171961219 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05119MinusP000Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP000Output2559.1‖ ≤ (batchValueN05119MinusP000Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP000BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP000Output2559,
    batchN05119MinusP000Center2559, batchN05119MinusP000Error2559, embedPair2542]

theorem batchValueN05119MinusP000Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP000Output2559.1) + embedPair2542
            batchValueN05119MinusP000Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨0, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP000Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP000Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP000Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP000Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP000Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP000Output2559, pairMagnitude2542]

def batchValueN05119MinusP001Output2559 : RatState2542 :=
  ((((34169022331674657308501850392852931 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((6872819360454070563190395423926039 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((6448840969194396923224843774095 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05119MinusP001Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP001Output2559.1‖ ≤ (batchValueN05119MinusP001Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP001BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP001Output2559,
    batchN05119MinusP001Center2559, batchN05119MinusP001Error2559, embedPair2542]

theorem batchValueN05119MinusP001Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP001Output2559.1) + embedPair2542
            batchValueN05119MinusP001Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨1, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP001Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP001Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP001Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP001Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP001Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP001Output2559, pairMagnitude2542]

def batchValueN05119MinusP002Output2559 : RatState2542 :=
  ((((68338158254347080611939487125973925 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-3436415392202059335222155730840303) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((3224425676717443754085083480953 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05119MinusP002Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP002Output2559.1‖ ≤ (batchValueN05119MinusP002Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP002BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP002Output2559,
    batchN05119MinusP002Center2559, batchN05119MinusP002Error2559, embedPair2542]

theorem batchValueN05119MinusP002Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP002Output2559.1) + embedPair2542
            batchValueN05119MinusP002Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨2, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP002Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP002Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP002Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP002Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP002Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP002Output2559, pairMagnitude2542]

def batchValueN05119MinusP003Output2559 : RatState2542 :=
  ((((68338221762420089606593694935436785 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-3436418585734416542388178396647095) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((6448857159203737902251197562095 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05119MinusP003Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP003Output2559.1‖ ≤ (batchValueN05119MinusP003Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP003BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP003Output2559,
    batchN05119MinusP003Center2559, batchN05119MinusP003Error2559, embedPair2542]

theorem batchValueN05119MinusP003Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP003Output2559.1) + embedPair2542
            batchValueN05119MinusP003Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨3, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP003Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP003Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP003Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP003Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP003Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP003Output2559, pairMagnitude2542]

def batchValueN05119MinusP004Output2559 : RatState2542 :=
  ((((68338259500788089704072508966229503 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((6872840966850856388607695027437749 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((3224430304581276660804530147649 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05119MinusP004Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP004Output2559.1‖ ≤ (batchValueN05119MinusP004Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP004BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP004Output2559,
    batchN05119MinusP004Center2559, batchN05119MinusP004Error2559, embedPair2542]

theorem batchValueN05119MinusP004Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP004Output2559.1) + embedPair2542
            batchValueN05119MinusP004Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨4, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP004Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP004Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP004Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP004Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP004Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP004Output2559, pairMagnitude2542]

def batchValueN05119MinusP005Output2559 : RatState2542 :=
  ((((68424262043146243304847327298652041 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((0 : ℚ) /
        1)),
    ((3073777350247193428604776321287 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05119MinusP005Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP005Output2559.1‖ ≤ (batchValueN05119MinusP005Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP005BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP005Output2559,
    batchN05119MinusP005Center2559, batchN05119MinusP005Error2559, embedPair2542]

theorem batchValueN05119MinusP005Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP005Output2559.1) + embedPair2542
            batchValueN05119MinusP005Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨5, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP005Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP005Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP005Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP005Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP005Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP005Output2559, pairMagnitude2542]

def batchValueN05119MinusP006Output2559 : RatState2542 :=
  ((((17106118510071582424137504584889959 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1)),
    ((12295146304184094802306035054029 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119MinusP006Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP006Output2559.1‖ ≤ (batchValueN05119MinusP006Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP006BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP006Output2559,
    batchN05119MinusP006Center2559, batchN05119MinusP006Error2559, embedPair2542]

theorem batchValueN05119MinusP006Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP006Output2559.1) + embedPair2542
            batchValueN05119MinusP006Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨6, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP006Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP006Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP006Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP006Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP006Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP006Output2559, pairMagnitude2542]

def batchValueN05119MinusP007Output2559 : RatState2542 :=
  ((((34212284074386526062500505013302701 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1)),
    ((3073790671506489248495012638049 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05119MinusP007Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP007Output2559.1‖ ≤ (batchValueN05119MinusP007Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP007BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP007Output2559,
    batchN05119MinusP007Center2559, batchN05119MinusP007Error2559, embedPair2542]

theorem batchValueN05119MinusP007Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP007Output2559.1) + embedPair2542
            batchValueN05119MinusP007Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨7, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP007Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP007Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP007Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP007Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP007Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP007Output2559, pairMagnitude2542]

def batchValueN05119MinusP008Output2559 : RatState2542 :=
  ((((68413135137079552770706605104777515 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((2475792387690418440733645206004697 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12511161947040972037249728888013 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119MinusP008Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP008Output2559.1‖ ≤ (batchValueN05119MinusP008Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP008BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP008Output2559,
    batchN05119MinusP008Center2559, batchN05119MinusP008Error2559, embedPair2542]

theorem batchValueN05119MinusP008Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP008Output2559.1) + embedPair2542
            batchValueN05119MinusP008Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨8, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP008Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP008Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP008Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP008Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP008Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP008Output2559, pairMagnitude2542]

def batchValueN05119MinusP009Output2559 : RatState2542 :=
  ((((68399563841778805320831794557230777 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((920477121588419990933635517418443 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((12616817366626715925935176043465 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119MinusP009Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP009Output2559.1‖ ≤ (batchValueN05119MinusP009Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP009BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP009Output2559,
    batchN05119MinusP009Center2559, batchN05119MinusP009Error2559, embedPair2542]

theorem batchValueN05119MinusP009Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP009Output2559.1) + embedPair2542
            batchValueN05119MinusP009Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨9, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP009Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP009Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP009Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP009Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP009Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP009Output2559, pairMagnitude2542]

def batchValueN05119MinusP010Output2559 : RatState2542 :=
  ((((68389273027037334110125418654915613 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((1095077748882371075366422795709885 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((12678122052529378217244052131603 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119MinusP010Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP010Output2559.1‖ ≤ (batchValueN05119MinusP010Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP010BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP010Output2559,
    batchN05119MinusP010Center2559, batchN05119MinusP010Error2559, embedPair2542]

theorem batchValueN05119MinusP010Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP010Output2559.1) + embedPair2542
            batchValueN05119MinusP010Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨10, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP010Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP010Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP010Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP010Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP010Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP010Output2559, pairMagnitude2542]

def batchValueN05119MinusP011Output2559 : RatState2542 :=
  ((((136762842509260362310953976544953545 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((4845894537794678362507774612692251 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12719041660541592984186397425229 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119MinusP011Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP011Output2559.1‖ ≤ (batchValueN05119MinusP011Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP011BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP011Output2559,
    batchN05119MinusP011Center2559, batchN05119MinusP011Error2559, embedPair2542]

theorem batchValueN05119MinusP011Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP011Output2559.1) + embedPair2542
            batchValueN05119MinusP011Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨11, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP011Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP011Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP011Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP011Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP011Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP011Output2559, pairMagnitude2542]

def batchValueN05119MinusP012Output2559 : RatState2542 :=
  ((((17093113333274168743473140176742453 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((5328065872176414572945352535907913 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12761462825337725864745839544313 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119MinusP012Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP012Output2559.1‖ ≤ (batchValueN05119MinusP012Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP012BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP012Output2559,
    batchN05119MinusP012Center2559, batchN05119MinusP012Error2559, embedPair2542]

theorem batchValueN05119MinusP012Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP012Output2559.1) + embedPair2542
            batchValueN05119MinusP012Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨12, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP012Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP012Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP012Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP012Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP012Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP012Output2559, pairMagnitude2542]

def batchValueN05119MinusP013Output2559 : RatState2542 :=
  ((((68363540785304809174710801069040455 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((5767404118669434242834954134771201 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((6400077247752853716294087521289 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05119MinusP013Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP013Output2559.1‖ ≤ (batchValueN05119MinusP013Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP013BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP013Output2559,
    batchN05119MinusP013Center2559, batchN05119MinusP013Error2559, embedPair2542]

theorem batchValueN05119MinusP013Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP013Output2559.1) + embedPair2542
            batchValueN05119MinusP013Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨13, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP013Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP013Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP013Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP013Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP013Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP013Output2559, pairMagnitude2542]

def batchValueN05119MinusP014Output2559 : RatState2542 :=
  ((((136690322917036379465415611784707965 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((6581292116332526340337433221276721 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((12871930907743310001781199682229 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119MinusP014Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP014Output2559.1‖ ≤ (batchValueN05119MinusP014Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP014BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP014Output2559,
    batchN05119MinusP014Center2559, batchN05119MinusP014Error2559, embedPair2542]

theorem batchValueN05119MinusP014Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP014Output2559.1) + embedPair2542
            batchValueN05119MinusP014Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨14, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP014Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP014Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP014Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP014Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP014Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP014Output2559, pairMagnitude2542]

def batchValueN05119MinusP015Output2559 : RatState2542 :=
  ((((136661005905620481834759904936433059 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((7164303870450030101716770460711611 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((403857064041269846621405252083 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168)))

theorem batchValueN05119MinusP015Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP015Output2559.1‖ ≤ (batchValueN05119MinusP015Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP015BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP015Output2559,
    batchN05119MinusP015Center2559, batchN05119MinusP015Error2559, embedPair2542]

theorem batchValueN05119MinusP015Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP015Output2559.1) + embedPair2542
            batchValueN05119MinusP015Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨15, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP015Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP015Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP015Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP015Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP015Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP015Output2559, pairMagnitude2542]

def batchValueN05119MinusP016Output2559 : RatState2542 :=
  ((((136638271243340928355018544145654227 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((1896388289541678470197733149321781 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((12960675035634320448554100562401 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119MinusP016Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP016Output2559.1‖ ≤ (batchValueN05119MinusP016Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP016BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP016Output2559,
    batchN05119MinusP016Center2559, batchN05119MinusP016Error2559, embedPair2542]

theorem batchValueN05119MinusP016Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP016Output2559.1) + embedPair2542
            batchValueN05119MinusP016Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨16, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP016Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP016Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP016Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP016Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP016Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP016Output2559, pairMagnitude2542]

def batchValueN05119MinusP017Output2559 : RatState2542 :=
  ((((8536900004882588456406383771233277 : ℚ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)),
    ((2100898492058081899089742025959593 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((13033111058234186885931559623125 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119MinusP017Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP017Output2559.1‖ ≤ (batchValueN05119MinusP017Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP017BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP017Output2559,
    batchN05119MinusP017Center2559, batchN05119MinusP017Error2559, embedPair2542]

theorem batchValueN05119MinusP017Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP017Output2559.1) + embedPair2542
            batchValueN05119MinusP017Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨17, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP017Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP017Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP017Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP017Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP017Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP017Output2559, pairMagnitude2542]

def batchValueN05119MinusP018Output2559 : RatState2542 :=
  ((((68285512529954108971620731390025879 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((8712800879746020555240806347520833 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((3265131410255233964747771445697 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05119MinusP018Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP018Output2559.1‖ ≤ (batchValueN05119MinusP018Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP018BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP018Output2559,
    batchN05119MinusP018Center2559, batchN05119MinusP018Error2559, embedPair2542]

theorem batchValueN05119MinusP018Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP018Output2559.1) + embedPair2542
            batchValueN05119MinusP018Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨18, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP018Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP018Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP018Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP018Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP018Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP018Output2559, pairMagnitude2542]

def batchValueN05119MinusP019Output2559 : RatState2542 :=
  ((((136534233555798974945647184761037397 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((2317876889724714927326394073006797 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744))),
    ((409690937536066655923181125097 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168)))

theorem batchValueN05119MinusP019Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP019Output2559.1‖ ≤ (batchValueN05119MinusP019Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP019BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP019Output2559,
    batchN05119MinusP019Center2559, batchN05119MinusP019Error2559, embedPair2542]

theorem batchValueN05119MinusP019Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP019Output2559.1) + embedPair2542
            batchValueN05119MinusP019Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨19, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP019Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP019Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP019Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP019Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP019Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP019Output2559, pairMagnitude2542]

def batchValueN05119MinusP020Output2559 : RatState2542 :=
  ((((136491631671103869188831385599620871 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((9878879938732765665723439748539677 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((13164085247522669006634164507403 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119MinusP020Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP020Output2559.1‖ ≤ (batchValueN05119MinusP020Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP020BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP020Output2559,
    batchN05119MinusP020Center2559, batchN05119MinusP020Error2559, embedPair2542]

theorem batchValueN05119MinusP020Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP020Output2559.1) + embedPair2542
            batchValueN05119MinusP020Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨20, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP020Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP020Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP020Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP020Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP020Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP020Output2559, pairMagnitude2542]

def batchValueN05119MinusP021Output2559 : RatState2542 :=
  ((((136454010412523374539035245978191931 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((10385606743139467390058717359548691 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((6604587085869879578309401578647 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05119MinusP021Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP021Output2559.1‖ ≤ (batchValueN05119MinusP021Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP021BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP021Output2559,
    batchN05119MinusP021Center2559, batchN05119MinusP021Error2559, embedPair2542]

theorem batchValueN05119MinusP021Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP021Output2559.1) + embedPair2542
            batchValueN05119MinusP021Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨21, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP021Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP021Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP021Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP021Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP021Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP021Output2559, pairMagnitude2542]

def batchValueN05119MinusP022Output2559 : RatState2542 :=
  ((((34108506643302950808937543788515145 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((5322456625100786892942830619525167 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((13232267893962419016699072549841 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119MinusP022Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP022Output2559.1‖ ≤ (batchValueN05119MinusP022Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP022BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP022Output2559,
    batchN05119MinusP022Center2559, batchN05119MinusP022Error2559, embedPair2542]

theorem batchValueN05119MinusP022Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP022Output2559.1) + embedPair2542
            batchValueN05119MinusP022Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨22, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP022Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP022Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP022Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP022Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP022Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP022Output2559, pairMagnitude2542]

def batchValueN05119MinusP023Output2559 : RatState2542 :=
  ((((136373651225292125419020342027441741 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((11392323580664353380926712831803879 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((13298909874679709891445635516237 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119MinusP023Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP023Output2559.1‖ ≤ (batchValueN05119MinusP023Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP023BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP023Output2559,
    batchN05119MinusP023Center2559, batchN05119MinusP023Error2559, embedPair2542]

theorem batchValueN05119MinusP023Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP023Output2559.1) + embedPair2542
            batchValueN05119MinusP023Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨23, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP023Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP023Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP023Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP023Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP023Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP023Output2559, pairMagnitude2542]

def batchValueN05119MinusP024Output2559 : RatState2542 :=
  ((((68172265935803253145831594145190809 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((5867844872622722568474542792324631 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((3332391190051878303674760602877 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05119MinusP024Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP024Output2559.1‖ ≤ (batchValueN05119MinusP024Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP024BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP024Output2559,
    batchN05119MinusP024Center2559, batchN05119MinusP024Error2559, embedPair2542]

theorem batchValueN05119MinusP024Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP024Output2559.1) + embedPair2542
            batchValueN05119MinusP024Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨24, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP024Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP024Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP024Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP024Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP024Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP024Output2559, pairMagnitude2542]

def batchValueN05119MinusP025Output2559 : RatState2542 :=
  ((((8519175001980677903851323210829031 : ℚ) /
        (9134385 * 10^40
        + 2333181432387730302044767688728495783936)),
    ((12166102506753169410234910000014849 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((13368025902742731320677342707611 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119MinusP025Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP025Output2559.1‖ ≤ (batchValueN05119MinusP025Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP025BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP025Output2559,
    batchN05119MinusP025Center2559, batchN05119MinusP025Error2559, embedPair2542]

theorem batchValueN05119MinusP025Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP025Output2559.1) + embedPair2542
            batchValueN05119MinusP025Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨25, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP025Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP025Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP025Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP025Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP025Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP025Output2559, pairMagnitude2542]

def batchValueN05119MinusP026Output2559 : RatState2542 :=
  ((((34066708954997666427244722471119259 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((12605841530492533156490411532062923 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((3351840201121234744157453580137 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344)))

theorem batchValueN05119MinusP026Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP026Output2559.1‖ ≤ (batchValueN05119MinusP026Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP026BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP026Output2559,
    batchN05119MinusP026Center2559, batchN05119MinusP026Error2559, embedPair2542]

theorem batchValueN05119MinusP026Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP026Output2559.1) + embedPair2542
            batchValueN05119MinusP026Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨26, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP026Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP026Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP026Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP026Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP026Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP026Output2559, pairMagnitude2542]

def batchValueN05119MinusP027Output2559 : RatState2542 :=
  ((((68103332828402352451152359566069131 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    ((6620083378243797487725404228405657 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488))),
    ((841510870720748436607015000339 : ℚ) /
        (10043362776618689222 * 10^40
        + 1372630771322662657637687111424552206336)))

theorem batchValueN05119MinusP027Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP027Output2559.1‖ ≤ (batchValueN05119MinusP027Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP027BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP027Output2559,
    batchN05119MinusP027Center2559, batchN05119MinusP027Error2559, embedPair2542]

theorem batchValueN05119MinusP027Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP027Output2559.1) + embedPair2542
            batchValueN05119MinusP027Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨27, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP027Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP027Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP027Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP027Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP027Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP027Output2559, pairMagnitude2542]

def batchValueN05119MinusP028Output2559 : RatState2542 :=
  ((((136182027442187757030512704326884739 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((13491226290423052758738845485893577 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((6743341875678270580910058172461 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)))

theorem batchValueN05119MinusP028Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP028Output2559.1‖ ≤ (batchValueN05119MinusP028Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP028BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP028Output2559,
    batchN05119MinusP028Center2559, batchN05119MinusP028Error2559, embedPair2542]

theorem batchValueN05119MinusP028Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP028Output2559.1) + embedPair2542
            batchValueN05119MinusP028Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨28, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP028Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP028Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP028Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP028Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP028Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP028Output2559, pairMagnitude2542]

def batchValueN05119MinusP029Output2559 : RatState2542 :=
  ((((136143628816801889985754233686278607 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((13873359999547748622963575466777233 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976))),
    ((13520971596804145523611194426485 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)))

theorem batchValueN05119MinusP029Error2559 :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP029Output2559.1‖ ≤ (batchValueN05119MinusP029Output2559.2 : ℝ)
                := by
  have h := batchN05119MinusP029BaseError2559
  convert h using 1
  all_goals norm_num [batchValueN05119MinusPosition2559, batchN05119MinusPosition2559,
      batchValueN05119MinusP029Output2559,
    batchN05119MinusP029Center2559, batchN05119MinusP029Error2559, embedPair2542]

theorem batchValueN05119MinusP029Norm2559 : ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05119MinusPosition2559‖ ≤ 1 := by
  calc
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05119MinusPosition2559‖ =
            ‖(weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP029Output2559.1) + embedPair2542
            batchValueN05119MinusP029Output2559.1‖ := by
      congr 1
      ring
    _ ≤ ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 ⟨29, by omega⟩ batchValueN05119MinusPosition2559 - embedPair2542
            batchValueN05119MinusP029Output2559.1‖ + ‖embedPair2542
            batchValueN05119MinusP029Output2559.1‖ := norm_add_le _ _
    _ ≤ (batchValueN05119MinusP029Output2559.2 : ℝ) + (pairMagnitude2542
        batchValueN05119MinusP029Output2559.1 : ℝ) :=
      add_le_add batchValueN05119MinusP029Error2559 (embedPair_magnitude2542 _)
    _ ≤ 1 := by norm_num [batchValueN05119MinusP029Output2559, pairMagnitude2542]

noncomputable def batchValueN05119MinusValue2559 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 batchValueN05119MinusP000Output2559.1
  | 1 => embedPair2542 batchValueN05119MinusP001Output2559.1
  | 2 => embedPair2542 batchValueN05119MinusP002Output2559.1
  | 3 => embedPair2542 batchValueN05119MinusP003Output2559.1
  | 4 => embedPair2542 batchValueN05119MinusP004Output2559.1
  | 5 => embedPair2542 batchValueN05119MinusP005Output2559.1
  | 6 => embedPair2542 batchValueN05119MinusP006Output2559.1
  | 7 => embedPair2542 batchValueN05119MinusP007Output2559.1
  | 8 => embedPair2542 batchValueN05119MinusP008Output2559.1
  | 9 => embedPair2542 batchValueN05119MinusP009Output2559.1
  | 10 => embedPair2542 batchValueN05119MinusP010Output2559.1
  | 11 => embedPair2542 batchValueN05119MinusP011Output2559.1
  | 12 => embedPair2542 batchValueN05119MinusP012Output2559.1
  | 13 => embedPair2542 batchValueN05119MinusP013Output2559.1
  | 14 => embedPair2542 batchValueN05119MinusP014Output2559.1
  | 15 => embedPair2542 batchValueN05119MinusP015Output2559.1
  | 16 => embedPair2542 batchValueN05119MinusP016Output2559.1
  | 17 => embedPair2542 batchValueN05119MinusP017Output2559.1
  | 18 => embedPair2542 batchValueN05119MinusP018Output2559.1
  | 19 => embedPair2542 batchValueN05119MinusP019Output2559.1
  | 20 => embedPair2542 batchValueN05119MinusP020Output2559.1
  | 21 => embedPair2542 batchValueN05119MinusP021Output2559.1
  | 22 => embedPair2542 batchValueN05119MinusP022Output2559.1
  | 23 => embedPair2542 batchValueN05119MinusP023Output2559.1
  | 24 => embedPair2542 batchValueN05119MinusP024Output2559.1
  | 25 => embedPair2542 batchValueN05119MinusP025Output2559.1
  | 26 => embedPair2542 batchValueN05119MinusP026Output2559.1
  | 27 => embedPair2542 batchValueN05119MinusP027Output2559.1
  | 28 => embedPair2542 batchValueN05119MinusP028Output2559.1
  | 29 => embedPair2542 batchValueN05119MinusP029Output2559.1
  | _ => 0

noncomputable def batchValueN05119MinusError2559 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (batchValueN05119MinusP000Output2559.2 : ℝ)
  | 1 => (batchValueN05119MinusP001Output2559.2 : ℝ)
  | 2 => (batchValueN05119MinusP002Output2559.2 : ℝ)
  | 3 => (batchValueN05119MinusP003Output2559.2 : ℝ)
  | 4 => (batchValueN05119MinusP004Output2559.2 : ℝ)
  | 5 => (batchValueN05119MinusP005Output2559.2 : ℝ)
  | 6 => (batchValueN05119MinusP006Output2559.2 : ℝ)
  | 7 => (batchValueN05119MinusP007Output2559.2 : ℝ)
  | 8 => (batchValueN05119MinusP008Output2559.2 : ℝ)
  | 9 => (batchValueN05119MinusP009Output2559.2 : ℝ)
  | 10 => (batchValueN05119MinusP010Output2559.2 : ℝ)
  | 11 => (batchValueN05119MinusP011Output2559.2 : ℝ)
  | 12 => (batchValueN05119MinusP012Output2559.2 : ℝ)
  | 13 => (batchValueN05119MinusP013Output2559.2 : ℝ)
  | 14 => (batchValueN05119MinusP014Output2559.2 : ℝ)
  | 15 => (batchValueN05119MinusP015Output2559.2 : ℝ)
  | 16 => (batchValueN05119MinusP016Output2559.2 : ℝ)
  | 17 => (batchValueN05119MinusP017Output2559.2 : ℝ)
  | 18 => (batchValueN05119MinusP018Output2559.2 : ℝ)
  | 19 => (batchValueN05119MinusP019Output2559.2 : ℝ)
  | 20 => (batchValueN05119MinusP020Output2559.2 : ℝ)
  | 21 => (batchValueN05119MinusP021Output2559.2 : ℝ)
  | 22 => (batchValueN05119MinusP022Output2559.2 : ℝ)
  | 23 => (batchValueN05119MinusP023Output2559.2 : ℝ)
  | 24 => (batchValueN05119MinusP024Output2559.2 : ℝ)
  | 25 => (batchValueN05119MinusP025Output2559.2 : ℝ)
  | 26 => (batchValueN05119MinusP026Output2559.2 : ℝ)
  | 27 => (batchValueN05119MinusP027Output2559.2 : ℝ)
  | 28 => (batchValueN05119MinusP028Output2559.2 : ℝ)
  | 29 => (batchValueN05119MinusP029Output2559.2 : ℝ)
  | _ => 0

theorem batchValueN05119MinusExp_error2559 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05119MinusPosition2559 -
            batchValueN05119MinusValue2559 i‖
            ≤ batchValueN05119MinusError2559 i := by
  fin_cases i
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP000Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP001Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP002Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP003Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP004Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP005Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP006Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP007Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP008Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP009Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP010Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP011Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP012Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP013Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP014Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP015Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP016Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP017Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP018Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP019Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP020Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP021Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP022Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP023Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP024Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP025Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP026Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP027Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP028Error2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP029Error2559

theorem batchValueN05119MinusUnit_norm2559 (i : Fin 30) :
    ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05119MinusPosition2559‖ ≤ 1 := by
  fin_cases i
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP000Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP001Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP002Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP003Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP004Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP005Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP006Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP007Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP008Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP009Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP010Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP011Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP012Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP013Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP014Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP015Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP016Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP017Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP018Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP019Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP020Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP021Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP022Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP023Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP024Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP025Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP026Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP027Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP028Norm2559
  · simpa only [batchValueN05119MinusValue2559, batchValueN05119MinusError2559] using
      batchValueN05119MinusP029Norm2559

noncomputable def batchValueN05119MinusSumValue2559 : ℂ := ⟨(((((344188671331620928295514326 *
    10^40
        + 9111299032394064472659161636061725999960) * 10^40
        + 8261414128238882002782776868025682649846) * 10^40
        + 9757245740695002981016826517404188990153) : ℝ) /
        (((24973988402527937851052777 * 10^40
        + 8383453304459887851413197692068732556770) * 10^40
        + 297391055812496096244882450793576927861) * 10^40
        + 5448971252983163583805434306282450321408)),
    (((((15803934098978430418346407 * 10^40
        + 8636166217760541668431932948104426413711) * 10^40
        + 6265370804555743447749963545316365318417) * 10^40
        + 2904446165745519883975035541990942812147) : ℝ) /
        (((24973988402527937851052777 * 10^40
        + 8383453304459887851413197692068732556770) * 10^40
        + 297391055812496096244882450793576927861) * 10^40
        + 5448971252983163583805434306282450321408))⟩

noncomputable def batchValueN05119MinusUpper2559 : ℝ := ((5518562839 : ℝ) /
        400000000)

theorem batchValueN05119MinusSum_eq2559 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05119MinusValue2559 i) =
      batchValueN05119MinusSumValue2559 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN05119MinusValue2559,
      batchValueN05119MinusSumValue2559, embedPair2542, batchValueN05119MinusP000Output2559,
      batchValueN05119MinusP001Output2559,
      batchValueN05119MinusP002Output2559,
      batchValueN05119MinusP003Output2559,
      batchValueN05119MinusP004Output2559,
      batchValueN05119MinusP005Output2559,
      batchValueN05119MinusP006Output2559,
      batchValueN05119MinusP007Output2559,
      batchValueN05119MinusP008Output2559,
      batchValueN05119MinusP009Output2559,
      batchValueN05119MinusP010Output2559,
      batchValueN05119MinusP011Output2559,
      batchValueN05119MinusP012Output2559,
      batchValueN05119MinusP013Output2559,
      batchValueN05119MinusP014Output2559,
      batchValueN05119MinusP015Output2559,
      batchValueN05119MinusP016Output2559,
      batchValueN05119MinusP017Output2559,
      batchValueN05119MinusP018Output2559,
      batchValueN05119MinusP019Output2559,
      batchValueN05119MinusP020Output2559,
      batchValueN05119MinusP021Output2559,
      batchValueN05119MinusP022Output2559,
      batchValueN05119MinusP023Output2559,
      batchValueN05119MinusP024Output2559,
      batchValueN05119MinusP025Output2559,
      batchValueN05119MinusP026Output2559,
      batchValueN05119MinusP027Output2559,
      batchValueN05119MinusP028Output2559,
      batchValueN05119MinusP029Output2559, Complex.mul_re, Complex.mul_im]

theorem batchValueN05119MinusSum_norm2559 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05119MinusValue2559 i‖ ≤
      ((68982035487 : ℝ) /
        5000000000) := by
  rw [batchValueN05119MinusSum_eq2559]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [batchValueN05119MinusSumValue2559]

theorem batchValueN05119MinusEvaluation_charge2559 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * batchValueN05119MinusError2559 i) ≤ (1 : ℝ)/10^12 :=
          by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, batchValueN05119MinusError2559,
      batchValueN05119MinusP000Output2559,
      batchValueN05119MinusP001Output2559,
      batchValueN05119MinusP002Output2559,
      batchValueN05119MinusP003Output2559,
      batchValueN05119MinusP004Output2559,
      batchValueN05119MinusP005Output2559,
      batchValueN05119MinusP006Output2559,
      batchValueN05119MinusP007Output2559,
      batchValueN05119MinusP008Output2559,
      batchValueN05119MinusP009Output2559,
      batchValueN05119MinusP010Output2559,
      batchValueN05119MinusP011Output2559,
      batchValueN05119MinusP012Output2559,
      batchValueN05119MinusP013Output2559,
      batchValueN05119MinusP014Output2559,
      batchValueN05119MinusP015Output2559,
      batchValueN05119MinusP016Output2559,
      batchValueN05119MinusP017Output2559,
      batchValueN05119MinusP018Output2559,
      batchValueN05119MinusP019Output2559,
      batchValueN05119MinusP020Output2559,
      batchValueN05119MinusP021Output2559,
      batchValueN05119MinusP022Output2559,
      batchValueN05119MinusP023Output2559,
      batchValueN05119MinusP024Output2559,
      batchValueN05119MinusP025Output2559,
      batchValueN05119MinusP026Output2559,
      batchValueN05119MinusP027Output2559,
      batchValueN05119MinusP028Output2559,
      batchValueN05119MinusP029Output2559]

theorem batchValueN05119MinusSigned_le2559 :
    signedJetUpper2539 0 ((((-1) : ℝ) /
        2)) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 batchValueN05119MinusPosition2559 ≤ batchValueN05119MinusUpper2559 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05119MinusPosition2559‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * batchValueN05119MinusValue2559 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * batchValueN05119MinusError2559 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (batchValueN05119MinusExp_error2559 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05119MinusPosition2559‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (batchValueN05119MinusUnit_norm2559 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 ((((-1) : ℝ) /
        2)) nodeModulation2541 i batchValueN05119MinusPosition2559‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 batchValueN05119MinusUpper2559
  linarith [batchValueN05119MinusSum_norm2559, batchValueN05119MinusEvaluation_charge2559]

theorem batchValueN05119MinusPhysical_le2559 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 ((((-1) : ℝ) /
        2)) coefficients nodeModulation2541 batchValueN05119MinusPosition2559‖ ≤
      batchValueN05119MinusUpper2559 := by
  have h := weightedPhysical2539_jet_le_center_error 0 ((((-1) : ℝ) /
        2)) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        batchValueN05119MinusPosition2559
  simpa only [iteratedDeriv_zero] using h.trans batchValueN05119MinusSigned_le2559

theorem batchValueN05119MinusGrid2559 :
    -stripRadius2303 + (5119 : ℝ)*(2*stripRadius2303/10240) = batchValueN05119MinusPosition2559 :=
        by
  norm_num [stripRadius2303, batchValueN05119MinusPosition2559]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchValueN05119MinusSigned_le2559
#print axioms ConnesWeilRH.Dev.batchValueN05119MinusPhysical_le2559
